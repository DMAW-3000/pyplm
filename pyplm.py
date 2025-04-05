
from copy import copy

from ply import yacc
from lexer import tokens, plmlexer
from compiler import *

# globals
g_pc = 0x0100
g_pc_save = g_pc
g_code = []
g_fout = None
g_label_n = 0
g_exec_state = False
g_state_count = 0
g_do_stack = []
g_first_do = True
g_case_flag = False
g_case_list = []
g_opt = False
g_data_init = False
g_sym_list = []
g_uni_list = []
g_anon_list = []
g_pseudo_count = 0
g_proc_list = []
g_proc_stack = []
g_ret = False
g_entry = None
g_flag_names = set(("ZERO", "CARRY", "SIGN", "PARITY"))

def lookup_sym(name):
    """Lookup symbol by name, with scope and precedence.
       Returns None if not found."""
    global g_sym_list, g_proc_list, g_proc_stack, g_anon_list, g_uni_list
        
    # search for variable as local
    # add current procedure name to enforce scope
    for proc in reversed(g_proc_stack):
        locname = "_%s_%s" % (proc, name)
        for sym in g_sym_list:
            if (locname == sym.name) and (not isinstance(sym, Label)):
                return sym
        for sym in g_uni_list:
            if locname == sym.name:
                return sym
    
    # search for variable as global
    for sym in g_sym_list:
        if (name == sym.name) and (not isinstance(sym, Label)):
            return sym
    for sym in g_uni_list:
        if name == sym.name:
            return sym
            
    # search procedure list
    for sym in reversed(g_proc_list):
        if name == sym.name:
            return sym
            
    # seach the anonymous variables
    for sym in g_anon_list:
        if name == sym.name:
            return sym
            
    # not found
    return None
    
    
def emit_code():
    """Commit the current block of compiled code to the symbol table.
       Each line is counted for tracking commited statements."""
    global g_pc, g_pc_save, g_code, g_sym_list, g_state_count
    if len(g_code) > 0:
        optimize()
        cdata = copy(g_code)
        g_sym_list.append(CodeBlock(g_pc_save, g_pc - g_pc_save, cdata))
        g_code.clear()
        g_state_count += 1
    g_pc_save = g_pc
    
    
def emit_label(name):
    """Add a new label to the symbol table at the current address"""
    global g_pc, g_sym_list, g_state_count
    emit_code()
    g_sym_list.append(Label(name, g_pc))
    g_state_count += 1
    
    
def new_label():
    """Create a unique label name"""
    global g_label_n
    s = "__L%05d" % g_label_n
    g_label_n += 1
    return s
    
    
def pop_statement():
    """Remove the symbols belonging to the last statement from the
       symbol table and return them to caller.  The current address
       is adjusted for code blocks returned."""
    global g_pc, g_sym_list, g_state_count, g_exec_state
    emit_code()
    sl = []
    if g_exec_state:
        for n in range(g_state_count):
            sym = g_sym_list.pop()
            if isinstance(sym, CodeBlock):
                g_pc -= sym.size
            sl.append(sym)
        sl.reverse()
    return sl
    
    
def mark_statement():
    """Mark the start of a new statement.  This mark is used by pop_statement()
       to determine which symbols to return."""
    global g_state_count
    emit_code()
    g_state_count = 0
    #print("MARK")
    
    
def emit_proc():
    """Output the current procedure code start label and the code necessary
       to save the input procedure args to variables."""
    global g_pc, g_code, g_proc_stack, g_sym_list, g_state_count
    global g_proc_list, g_entry
    
    # the first statement of the procedure has just been emmitted
    # rewind so that the procedure label and args code can be inserted
    es = pop_statement()
    procName = g_proc_stack[-1]
    #print("PROC:", procName, len(g_proc_stack))
    emit_label(procName)
    oldpc = g_pc
    for proc in g_proc_list:
        if proc.name == procName:
            break
        
    # optional entry handling
    if proc.name == g_entry:
        g_code.append("LXI H,__ENDCOM  ; exit address")
        g_code.append("PUSH H")
        g_pc += 4
        
    if proc.num_args > 0:
    
        # generate code to save proc first arg - in (D),E
        arg = lookup_sym(proc.arg_names[0])
        if arg is None:
            fatal("cannot find argument %s for procedure %s" % (argName, procName))
        if arg.size == 1:
            g_code.append("LXI H,%s  ; store proc arg 1" % arg.name)
            g_code.append("MOV M,E")
            g_pc += 4
        else:
            g_code.append("XCHG")
            g_code.append("SHLD %s  ; store proc arg 1" % arg.name)
            g_pc += 4
            
        # generate code to save proc second arg - in (B),C
        if proc.num_args >= 2:
            arg = lookup_sym(proc.arg_names[1])
            if arg is None:
                fatal("cannot find argument %s for procedure %s" % (argName, procName))
            if arg.size == 1:
                g_code.append("LXI H,%s  ; store proc arg 2" % arg.name)
                g_code.append("MOV M,C")
                g_pc += 4
            else:
                g_code.append("MOV L,C")
                g_code.append("MOV H,B")
                g_code.append("SHLD %s  ; store proc arg 2" % arg.name)
                g_pc += 5
                
        # generate code to save proc third+ args - on stack at SP + 2 in reverse order
        if proc.num_args > 2:
            g_code.append("LXI H,00002H  ; get ext args on stack")
            g_code.append("DAD SP")
            g_pc += 4
            names = list(proc.arg_names[2:])
            names.reverse()
            for n in names:
                arg = lookup_sym(n)
                if arg is None:
                    fatal("cannot find argument %s for procedure %s" % (argName, procName))
                g_code.append("MOV A,M  ; proc ext arg load")
                g_code.append("STA %s  ; assign LSB" % arg.name)
                g_pc += 4
                if arg.size == 1:
                    if n != names[-1]:
                        g_code.append("INX H  ; skip to next arg")
                        g_pc += 1
                else:
                    g_code.append("INX H")
                    g_code.append("MOV A,M")
                    g_code.append("STA %s+1  ; assign MSB" % arg.name)
                    g_pc += 5
    emit_code()
    
    # restore the first statement of the procedure
    size = g_pc - oldpc
    mark_statement()
    for sym in es:
        if isinstance(sym, CodeBlock):
            g_pc += sym.size
        sym.addr += size
        g_sym_list.append(sym)
        g_state_count += 1
        
    
def p_statements(p):
    '''statements : statements statement
                  | statement'''
                  
    
def p_statement(p):
    r'''statement : declare_statement
                  | label_statement
                  | code_statement'''
    p[0] = p[1]
    
                  
def p_code_statement(p):
    r'''code_statement : control_statement
                       | exec_statement'''
    global g_exec_state, g_proc_stack, g_case_flag, g_code, g_pc
    global g_case_list, g_sym_list, g_state_count
    if not g_exec_state:
        g_exec_state = True
        if len(g_proc_stack) > 0:
            emit_proc()
    if g_case_flag:
        cl = g_case_list[-1]
        if cl[1]:
            cl[1] = False
        else:
            label = new_label()
            es = pop_statement()
            cl[2].append(label)
            emit_label(label)
            for sym in es:
                if isinstance(sym, CodeBlock):
                    g_pc += sym.size
                g_sym_list.append(sym)
                g_state_count += 1
            g_code.append("JMP %s  ; end CASE" % cl[2][0])
            g_pc += 3
    p[0] = p[1]
                  
                  
def p_control_statement(p):
    r'''control_statement : if_then_statement
                          | else_statement
                          | do_while_statement
                          | do_to_statement
                          | do_case_statement'''
    p[0] = p[1]
    
                      
def p_exec_statement(p):
    r'''exec_statement : end_statement
                       | goto_statement
                       | do_statement
                       | assign_statement
                       | call_statement
                       | return_statement'''
    p[0] = p[1]
    
                  
def p_label_statement(p):
    r'''label_statement : IDENT COLON'''
    global g_sym_list
    if lookup_sym(p[1]) is not None:
        fatal("name %s already defined, line %d" % (p[1], p.lineno(1)))
    emit_label(p[1])
    print("declare label:", g_sym_list[-1])
    
   
def p_declare_statement(p):
    r'''declare_statement : DECLARE declare_list SEMICOLON
                          | declare_procedure
                          | end_procedure'''
    global g_exec_state
    g_exec_state = False
    mark_statement()
    
    
def p_declare_list(p):
    '''declare_list : declare_list1 declare_name
                    | declare_name'''


def p_declare_list1(p):
    r'''declare_list1 : declare_list1 declare_name COMMA
                      | declare_name COMMA'''
    
    
def p_declare_name(p):
    r'''declare_name : declare_literal
                     | declare_variable
                     | declare_variable_list
                     | declare_variable_init
                     | declare_variable_at
                     | declare_variable_based 
                     | declare_variable_ext
                     | declare_array
                     | declare_array_init1
                     | declare_array_init2
                     | declare_string
                     | declare_array_at
                     | declare_array_based
                     | declare_array_ext
                     | declare_struct_based'''
    
    
def p_declare_literal(p):
    r'''declare_literal : IDENT LITERALLY STRING'''
    print("declare literal: %s = \'%s\'" % (p[1], p[3]))
    
    
def p_variable_type(p):
    r'''variable_type : BYTE 
                      | ADDRESS'''
    p[0] = p[1]
    
    
def check_args(name, size):
    """Check the current procedure to see if this variable is a argument.
       If so, record argument variable size."""
    global g_proc_stack, g_proc_list
    for proc in g_proc_list:
        if proc.name == g_proc_stack[-1]:
            for n in range(proc.num_args):
                if proc.arg_names[n] == name:
                    proc.arg_widths[n] = size
                    
    
def p_declare_variable(p):
    r'''declare_variable : IDENT variable_type'''
    global g_uni_list, g_proc_stack
    if p[2] == 'BYTE':
        size = 1
    else:
        size = 2
    if len(g_proc_stack) > 0:
        check_args(p[1], size)
        name = "_%s_%s" % (g_proc_stack[-1], p[1])
    else:
        name = p[1]
    if lookup_sym(name) is not None:
        fatal("name %s already defined, line %d" % (name, p.lineno(1)))
    if len(g_proc_stack) > 0:
        proc = lookup_sym(g_proc_stack[-1])
        if isinstance(proc, ExternalProcedure):
            return
    g_uni_list.append(Variable(name, 0, size, None))
    print("declare variable:", g_uni_list[-1])
    
    
def p_declare_variable_list(p):
    r'''declare_variable_list : LPARENS vars_list RPARENS variable_type'''
    global g_uni_list, g_proc_stack
    if p[4] == 'BYTE':
        size = 1
    else:
        size = 2
    for name in p[2]:
        if len(g_proc_stack) > 0:
            check_args(name, size)
            name = "_%s_%s" % (g_proc_stack[-1], name)
        g_uni_list.append(Variable(name, 0, size, None))
        print("declare variable", g_uni_list[-1])
    
    
def p_vars_list(p):
    r'''vars_list : vars_list1 IDENT'''
    p[1].append(p[2])
    p[0] = p[1]
    
                                   
def p_vars_list1(p):
    r'''vars_list1 : vars_list1 IDENT COMMA
                   | IDENT COMMA'''
    if len(p) == 3:
        p[0] = [p[1]]
    else:
        p[1].append(p[2])
        p[0] = p[1]
    
    
def p_declare_variable_init(p):
    r'''declare_variable_init : IDENT variable_type DATA LPARENS init_data RPARENS'''
    global g_pc, g_sym_list
    if len(g_proc_stack) > 0:
        name = "_%s_%s" % (g_proc_stack[-1], p[1])
    else:
        name = p[1]
    if lookup_sym(name) is not None:
        fatal("name %s already defined, line %d" % (p[1], p.lineno(1)))
    if p[2] == 'BYTE':
        if isinstance(p[5], str):
            fatal("BYTE variables cannot initialize with references")
        size = 1
    else:
        size = 2
    g_sym_list.append(Variable(name, g_pc, size, p[5]))
    g_pc += size
    print("declare variable:", g_sym_list[-1])
    
    
def p_declare_variable_at(p):
    r'''declare_variable_at : IDENT variable_type AT LPARENS init_data RPARENS
                            | IDENT variable_type AT LPARENS PERIOD IDENT LPARENS number RPARENS RPARENS'''
    global g_sym_list, g_proc_stack
    if len(g_proc_stack) > 0:
        name = "_%s_%s" % (g_proc_stack[-1], p[1])
    else:
        name = p[1]
    if lookup_sym(name) is not None:
        fatal("name %s already defined, line %d" % (p[1], p.lineno(1)))
    if p[2] == 'BYTE':
        size = 1
    else:
        size = 2
    if len(p) == 7:
        ref = p[5]
        idx = 0
    else:
        sym = lookup_sym(p[6])
        if not isinstance(sym, Array):
            fatal("AT target %s not an array, line %d" % (p[6], p.lineno(6)))
        if (size != sym.elem_size):
            warning("AT target %s width different than variable, line %d" % (p[6], p.lineno(6)))
        idx = p[8] * sym.elem_size
        ref = sym.name
    g_sym_list.append(AtVariable(name, ref, size, idx))
    print("declare variable:", g_sym_list[-1])
    
    
def p_declare_variable_based(p):
    r'''declare_variable_based : IDENT BASED IDENT variable_type'''
    global g_sym_list, g_proc_stack
    if p[4] == 'BYTE':
        size = 1
    else:
        size = 2
    if len(g_proc_stack) > 0:
        check_args(p[1], size)
        name = "_%s_%s" % (g_proc_stack[-1], p[1])
    else:
        name = p[1]
    if lookup_sym(name) is not None:
        fatal("name %s already defined, line %d" % (name, p.lineno(1)))
    sym = lookup_sym(p[3])
    if sym is None:
        fatal("target variable %s does not exist, line %d" % (p[3], p.lineno(3)))
    if (not isinstance(sym, Variable)) or isinstance(sym, Array) or (sym.size != 2):
        fatal("target variable %s not ADDRESS, line %d" % (p[3], p.lineno(3)))
    g_sym_list.append(BasedVariable(name, sym.name, size, None))
    print("declare variable:", g_sym_list[-1])
    
    
def p_declare_variable_ext(p):
    r'''declare_variable_ext : IDENT variable_type EXTERNAL'''
    global g_sym_list, g_proc_stack
    name = p[1]
    if lookup_sym(name) is not None:
        fatal("name %s already defined, line %d" % (name, p.lineno(1)))
    if p[2] == 'BYTE':
        size = 1
    else:
        size = 2
    g_sym_list.append(AtVariable(name, name, size, None))
    print("declare variable:", g_sym_list[-1])

def p_init_data(p):
    r'''init_data : number
                  | reference'''
    p[0] = p[1]
    
    
def p_declare_array(p):
    r'''declare_array : IDENT LPARENS number RPARENS variable_type'''
    global g_uni_list, g_proc_stack
    if len(g_proc_stack) > 0:
        name = "_%s_%s" % (g_proc_stack[-1], p[1])
    else:
        name = p[1]
    if lookup_sym(name) is not None:
        fatal("name %s already defined, line %d" % (p[1], p.lineno(1)))
    if p[3] > 0xffff:
        fatal("array %s size too large, line %d" % (p[1], p.lineno(1)))
    if p[5] == 'BYTE':
        elementSize = 1
    else:
        elementSize = 2
    size = p[3] * elementSize
    g_uni_list.append(Array(name, 0, size, None, elementSize))
    print("declare array:", g_uni_list[-1])
    
    
def p_declare_array_init1(p):
    r'''declare_array_init1 : IDENT LPARENS array_init_list RPARENS variable_type'''
    global g_pc, g_sym_list, g_proc_stack
    if len(g_proc_stack) > 0:
        name = "_%s_%s" % (g_proc_stack[-1], p[1])
    else:
        name = p[1]
    if lookup_sym(name) is not None:
        fatal("name %s already defined, line %d" % (p[1], p.lineno(1)))
    if p[5] == 'BYTE':
        elementSize = 1
        for b in p[3]:
            if isinstance(b, Reference):
                fatal("BYTE variables cannot initialize with references")
    else:
        elementSize = 2
    size = len(p[3]) * elementSize
    g_sym_list.append(Array(name, g_pc, size, p[3], elementSize))
    g_pc += size
    print("declare array:", g_sym_list[-1])
    
    
def p_declare_array_init2(p):
    r'''declare_array_init2 : IDENT LPARENS number RPARENS variable_type DATA LPARENS array_init_list RPARENS'''
    global g_pc, g_sym_list, g_proc_stack
    if len(g_proc_stack) > 0:
        name = "_%s_%s" % (g_proc_stack[-1], p[1])
    else:
        name = p[1]
    if lookup_sym(name) is not None:
        fatal("name %s already defined, line %d" % (p[1], p.lineno(1)))
    if p[5] == 'BYTE':
        elementSize = 1
        for b in p[8]:
            if isinstance(b, Reference):
                fatal("BYTE variables cannot initialize with references")
    else:
        elementSize = 2
    size = p[3] * elementSize
    g_sym_list.append(Array(name, g_pc, size, p[8], elementSize))
    g_pc += size
    print("declare array:", g_sym_list[-1])
    
    
def p_array_init_list(p):
    r'''array_init_list : array_init_list1 array_init_data
                        | array_init_data'''
    if len(p) == 2:
        p[0] = [p[1]]
    else:
        p[1].append(p[2])
        p[0] = p[1]
     
     
def p_array_init_list1(p):
    r'''array_init_list1 : array_init_list1 array_init_data COMMA
                         | array_init_data COMMA'''
    if len(p) == 3:
        p[0] = [p[1]]
    else:
        p[1].append(p[2])
        p[0] = p[1]

     
def p_array_init_data(p):
    r'''array_init_data : init_data
                        | STRING'''
    p[0] = p[1]
 
 
def p_declare_string(p):
    r'''declare_string : IDENT LPARENS ASTERIX RPARENS variable_type DATA LPARENS STRING RPARENS
                       | IDENT LPARENS ASTERIX RPARENS variable_type DATA LPARENS array_init_list RPARENS'''
    global g_pc, g_sym_list, g_proc_stack
    if len(g_proc_stack) > 0:
        name = "_%s_%s" % (g_proc_stack[-1], p[1])
    else:
        name = p[1]
    if lookup_sym(name) is not None:
        fatal("name %s already defined, line %d" % (p[1], p.lineno(1)))
    if p[5] == 'BYTE':
        elementSize = 1
    else:
        elementSize = 2
    init = p[8]
    size = 0
    data = []
    if isinstance(init, str):
        for c in init:
            data.append(ord(c))
            size += 1
    else:
        data = []
        for d in init:
            if isinstance(d, str):
                for c in d:
                    data.append(ord(c))
                    size += 1
            else:
                data.append(d)
                size += elementSize
            
    g_sym_list.append(Array(name, g_pc, size, data, elementSize))
    g_pc += size
    print("declare string:", g_sym_list[-1])
   
   
def p_declare_array_at(p):
    r'''declare_array_at : IDENT LPARENS number RPARENS variable_type AT LPARENS init_data RPARENS'''
    global g_sym_list, g_proc_stack
    if len(g_proc_stack) > 0:
        name = "_%s_%s" % (g_proc_stack[-1], p[1])
    else:
        name = p[1]
    if lookup_sym(name) is not None:
        fatal("name %s already defined, line %d" % (p[1], p.lineno(1)))
    if p[5] == 'BYTE':
        elementSize = 1
    else:
        elementSize = 2
    size = p[3] * elementSize
    g_sym_list.append(AtArray(name, p[8], size, None, elementSize))
    print("declare array:", g_sym_list[-1])
    
    
def p_declare_array_based(p):
    r'''declare_array_based : IDENT BASED IDENT LPARENS number RPARENS variable_type'''
    global g_sym_list, g_proc_stack
    if len(g_proc_stack) > 0:
        name = "_%s_%s" % (g_proc_stack[-1], p[1])
    else:
        name = p[1]
    if lookup_sym(name) is not None:
        fatal("name %s already defined, line %d" % (p[1], p.lineno(1)))
    if p[7] == 'BYTE':
        elementSize = 1
    else:
        elementSize = 2
    size = p[5] * elementSize
    sym = lookup_sym(p[3])
    if sym is None:
        fatal("target variable %s does not exist, line %d" % (p[3], p.lineno(3)))
    if (not isinstance(sym, Variable)) or isinstance(sym, Array) or (sym.size != 2):
        fatal("target variable %s not ADDRESS, line %d" % (p[3], p.lineno(3)))
    g_sym_list.append(BasedArray(name, sym.name, size, None, elementSize))
    print("declare array:", g_sym_list[-1])
    
    
def p_declare_array_ext(p):
    r'''declare_array_ext : IDENT LPARENS number RPARENS variable_type EXTERNAL'''
    global g_sym_list, g_proc_stack
    name = p[1]
    if lookup_sym(name) is not None:
        fatal("name %s already defined, line %d" % (p[1], p.lineno(1)))
    if p[5] == 'BYTE':
        elementSize = 1
    else:
        elementSize = 2
    size = p[3] * elementSize
    g_sym_list.append(AtArray(name, name, size, None, elementSize))
    print("declare array:", g_sym_list[-1])
    
    
def p_declare_struct_based(p):
    r'''declare_struct_based : IDENT BASED IDENT STRUCTURE LPARENS struct_list RPARENS'''
    global g_sym_list, g_proc_stack
    if len(g_proc_stack) > 0:
        name = "_%s_%s" % (g_proc_stack[-1], p[1])
    else:
        name = p[1]
    if lookup_sym(name) is not None:
        fatal("name %s already defined, line %d" % (p[1], p.lineno(1)))
    smap = {}
    offset = 0
    for item in p[6]:
        if item[1] == 'BYTE':
            size = 1
        else:
            size = 2
        smap[item[0]] = (offset, size)
        offset += size
    g_sym_list.append(BasedStruct(name, p[3], offset, smap))
    print("declare struct:", g_sym_list[-1])
    
def p_struct_list(p):
    r'''struct_list : struct_list1 IDENT variable_type
                    | IDENT variable_type'''
    if len(p) == 3:
        p[0] = [(p[1], p[2])]
    else:
        p[1].append((p[2], p[3]))
        p[0] = p[1]
              
              
def p_struct_list1(p):
    r'''struct_list1 : struct_list1 IDENT variable_type COMMA
                     | IDENT variable_type COMMA'''
    if len(p) == 4:
        p[0] = [(p[1], p[2])]
    else:
        p[1].append((p[2], p[3]))
        p[0] = p[1]
    
    
def p_declare_procedure(p):
    r'''declare_procedure : procedure_arg0
                          | procedure_arg0_noret
                          | procedure_arg1
                          | procedure_arg1_noret
                          | procedure_arg2
                          | procedure_arg2_ext
                          | procedure_arg2_noret
                          | procedure_arg2_noret_ext
                          | procedure_arg3
                          | procedure_arg3_noret'''
                          
    
def p_procedure_arg0(p):
    r'''procedure_arg0 : IDENT COLON PROCEDURE variable_type SEMICOLON'''
    global g_proc_list, g_proc_stack
    if p[4] == 'BYTE':
        size = 1
    else:
        size = 2
    g_proc_list.append(UserProcedure(p[1], 0, size))
    g_proc_stack.append(p[1])
    print("declare procedure", g_proc_list[-1])
    
    
def p_procedure_arg0_noret(p):
    r'''procedure_arg0_noret : IDENT COLON PROCEDURE SEMICOLON'''
    global g_proc_list, g_proc_stack
    g_proc_list.append(UserProcedure(p[1], 0, 0))
    g_proc_stack.append(p[1])
    print("declare procedure", g_proc_list[-1])
    
    
def p_procedure_arg1(p):
    r'''procedure_arg1 : IDENT COLON PROCEDURE LPARENS IDENT RPARENS variable_type SEMICOLON'''
    global g_proc_list, g_proc_stack
    if p[7] == 'BYTE':
        size = 1
    else:
        size = 2
    g_proc_list.append(UserProcedure(p[1], 1, size, (p[5],)))
    g_proc_stack.append(p[1])
    print("declare procedure", g_proc_list[-1])
    
    
def p_procedure_arg1_noret(p):
    r'''procedure_arg1_noret : IDENT COLON PROCEDURE LPARENS IDENT RPARENS SEMICOLON'''
    global g_proc_list, g_proc_stack
    g_proc_list.append(UserProcedure(p[1], 1, 0, (p[5],)))
    g_proc_stack.append(p[1])
    print("declare procedure", g_proc_list[-1])
    
    
def p_procedure_arg2(p):
    r'''procedure_arg2 : IDENT COLON PROCEDURE LPARENS IDENT COMMA IDENT RPARENS variable_type SEMICOLON'''
    global g_proc_list, g_proc_stack
    if p[9] == 'BYTE':
        size = 1
    else:
        size = 2
    g_proc_list.append(UserProcedure(p[1], 2, size, (p[5],p[7])))
    g_proc_stack.append(p[1])
    print("declare procedure", g_proc_list[-1])
    
    
def p_procedure_arg2_noret(p):
    r'''procedure_arg2_noret : IDENT COLON PROCEDURE LPARENS IDENT COMMA IDENT RPARENS SEMICOLON'''
    global g_proc_list, g_proc_stack
    g_proc_list.append(UserProcedure(p[1], 2, 0, (p[5],p[7])))
    g_proc_stack.append(p[1])
    print("declare procedure", g_proc_list[-1])
    
    
def p_procedure_arg2_ext(p):
    '''procedure_arg2_ext : IDENT COLON PROCEDURE LPARENS IDENT COMMA IDENT RPARENS variable_type EXTERNAL SEMICOLON''' 
    global g_proc_list, g_proc_stack
    if p[9] == 'BYTE':
        size = 1
    else:
        size = 2
    g_proc_list.append(ExternalProcedure(p[1], 2, size, (p[5],p[7])))
    g_proc_stack.append(p[1])
    print("declare procedure", g_proc_list[-1])
    
    
def p_procedure_arg2_noret_ext(p):
    r'''procedure_arg2_noret_ext : IDENT COLON PROCEDURE LPARENS IDENT COMMA IDENT RPARENS EXTERNAL SEMICOLON'''
    global g_proc_list, g_proc_stack
    g_proc_list.append(ExternalProcedure(p[1], 2, 0, (p[5],p[7])))
    g_proc_stack.append(p[1])
    print("declare procedure", g_proc_list[-1])
    
    
def p_procedure_arg3(p):
    r'''procedure_arg3 : IDENT COLON PROCEDURE LPARENS IDENT COMMA IDENT COMMA IDENT RPARENS variable_type SEMICOLON'''
    global g_proc_list, g_proc_stack
    if p[11] == 'BYTE':
        size = 1
    else:
        size = 2
    g_proc_list.append(UserProcedure(p[1], 3, size, (p[5],p[7],p[9])))
    g_proc_stack.append(p[1])
    print("declare procedure", g_proc_list[-1])
    
    
def p_procedure_arg3_noret(p):
    r'''procedure_arg3_noret : IDENT COLON PROCEDURE LPARENS IDENT COMMA IDENT COMMA IDENT RPARENS SEMICOLON'''
    g_proc_list.append(UserProcedure(p[1], 3, 0, (p[5],p[7],p[9])))
    g_proc_stack.append(p[1])
    print("declare procedure", g_proc_list[-1])
    
    
def p_do_statement(p):
    r'''do_statement : DO SEMICOLON'''
    global g_do_stack, g_first_do
    #print("DO")
    mark_statement()
    if not g_first_do:
        g_first_do = False
    g_do_stack.append(None)  
    p[0] = 1
    
    
def p_cond_expr(p):
    r'''cond_expr : rel_expr
                  | bool_expr
                  | logic_expr'''
    p[0] = p[1]
    
        
def p_do_while_statement(p):
    r'''do_while_statement : DO WHILE cond_expr SEMICOLON'''
    global g_pc, g_code, g_do_stack, g_sym_list
    #print("DOWHILE:", p[3])
    mark_statement()
    label1 = new_label()
    label2 = new_label()
    emit_label(label1)
    collapse_left(p[3])
    g_code.append("XRA A  ; A = 0")
    g_code.append("CMP E  ; rel result")
    g_code.append("JZ %s  ; skip while" % label2)
    g_pc += 5
    g_do_stack.append((label2, label1))
    p[0] = 0
    
    
def p_do_case_statement(p):
    r'''do_case_statement : DO CASE expr SEMICOLON'''
    global g_pc, g_code, g_do_stack, g_case_flag, g_case_list
    print("DOCASE:", p[3])
    mark_statement()
    label1 = new_label()
    label2 = new_label()
    width = collapse_left(p[3])
    if width == 1:
        g_code.append("MVI D,000H  ; zero pad CASE MSB")
        g_pc += 2
    g_code.append("LXI H,%s  ; CASE table" % label1)
    g_code.append("XCHG")
    g_code.append("DAD H  ; index << 1")
    g_code.append("DAD D  ; CASE table offset")
    g_code.append("MOV E,M")
    g_code.append("INX H")
    g_code.append("MOV D,M")
    g_code.append("XCHG")
    g_code.append("PCHL  ; go to CASE")
    g_pc += 12
    g_do_stack.append((label2,))
    g_case_flag = True
    g_case_list.append([label1, True, [label2]])
    p[0] = 0;
    
    
def p_do_to_statement(p):
    r'''do_to_statement : DO IDENT EQUAL expr TO expr SEMICOLON
                        | DO IDENT EQUAL expr TO expr BY expr SEMICOLON'''
    global g_pc, g_code, g_do_stack
    #print("DOTO: %s %s %s" % (p[2], p[4], p[6]))
    if not isinstance(p[2], int):
        sym = lookup_sym(p[2])
        if not isinstance(sym, Variable):
            fatal("unknown identifier %s, line %d" % (p[2], p.lineno(1)))
        if isinstance(sym, Array):
            fatal("DO variable %s must be scalar, line %d" % (p[2], p.lineno(1)))
    mark_statement()
    label1 = new_label()
    label2 = new_label()
    label3 = new_label()
    toWidth = collapse_left(p[4])
    if toWidth > sym.size:
        fatal("DO variable %s overflow, line %d" % (p[2], p.lineno(1)))
    if sym.size == 1:
        g_code.append("MOV A,E")
        g_pc += 1
    else:
        if toWidth == 1:
            g_code.append("MVI D,000H  ; zero pad MSB")
            g_pc += 2
        g_code.append("XCHG     ; from D,E")
        g_pc += 1
    g_code.append("JMP %s  ; DO first iter" % label3)
    g_pc += 3
    emit_label(label1)
    toWidth = collapse_left(p[6])
    if toWidth > sym.size:
        fatal("DO variable %s overflow, line %d" % (p[2], p.lineno(1)))
    byFlag = (len(p) == 10) and (not isinstance(p[8], int))
    if byFlag:
        leftFlag = isinstance(p[8][0], Operator)
        if leftFlag:
            g_code.append("PUSH D  ; save left DO")
            g_pc += 1
        byWidth = collapse_right(p[8])
        if byWidth > sym.size:
            fatal("DO variable %s overflow, line %d" % (p[2], p.lineno(1)))
        if leftFlag:
            g_code.append("POP D  ; restore left DO")
            g_pc += 1
    if sym.size == 1:
        g_code.append("LDA %s  ; DO load" % sym.name)
        g_pc += 3
        if len(p) == 10:
            if byFlag:
                g_code.append("ADD C  ; DO update")
                g_pc += 1
            else:
                g_code.append("ADI %03XH  ; DO update" % p[8])
                g_pc += 2
        else:
            g_code.append("INR A   ; DO update")
            g_pc += 1
        g_code.append("CMP E   ; DO <=")
        g_code.append("JZ %s   ; = " % label3)
        g_code.append("JNC %s  ; > DO complete" % label2)
        g_pc += 7
    else:
        label4 = new_label()
        if byFlag and (byWidth == 1):
            g_code.append("MVI B,000H  ; zero pad MSB")
            g_pc += 2
        if toWidth == 1:
            g_code.append("MVI D,000H  ; zero pad MSB")
            g_pc += 2
        g_code.append("LHLD %s  ; DO load" % sym.name)
        g_pc += 3
        if len(p) == 10:
            if byFlag:
                g_code.append("DAD B  ; DO update")
                g_pc += 1
            else:
                g_code.append("LXI B,%05XH" % p[8])
                g_code.append("DAD B  ; DO update")
                g_pc += 4
        else:
            g_code.append("INX H    ; DO update")
            g_pc += 1
        g_code.append("MOV A,H")
        g_code.append("CMP D   ; DO <=")
        g_code.append("JZ %s   ; =" % label4)
        g_code.append("JNC %s  ; > DO complete" % label2)
        g_code.append("JMP %s  ; <" % label3)
        g_pc += 11
        emit_label(label4)
        g_code.append("MOV A,L")
        g_code.append("CMP E   ; DO <=")
        g_code.append("JZ %s   ; =" % label3)
        g_code.append("JNC %s  ; > DO complete" % label2)
        g_pc += 8
    emit_label(label3)
    if sym.size == 1:
        g_code.append("STA %s  ; DO assign" % sym.name)
        g_pc += 3
    else:
        g_code.append("SHLD %s  ; DO assign" % sym.name)
        g_pc += 3
    g_do_stack.append((label2,label1))
    p[0] = 0
    
    
def p_end_statement(p):
    r'''end_statement : END SEMICOLON'''
    global g_do_stack, g_pc, g_code, g_case_flag
    try:
        labels = g_do_stack.pop()
    except IndexError:
        fatal("unmatched END, line %d" % p.lineno(1))
    mark_statement()
    if labels is not None:
        if len(labels) > 1:
            g_code.append("JMP %s  ; END" % labels[1])
            g_pc += 3
        if isinstance(labels[0], tuple):
            for l in labels[0]:
                emit_label(l)
        else:
            emit_label(labels[0])
    if g_case_flag:
        g_case_flag = False
    p[0] = 0
    

def p_end_procedure(p):
    r'''end_procedure : END IDENT SEMICOLON'''
    global g_proc_stack, g_code, g_pc, g_ret
    try:
        top = g_proc_stack.pop()
    except IndexError:
        fatal("unmatched END, line %s" % p.lineno(2))
    if (top is None) or (p[2] != top):
        fatal("unmatched END, line %s" % p.lineno(2))
    proc = lookup_sym(top)
    if not isinstance(proc, ExternalProcedure):
        if (not g_ret) and (proc.size != 0):
            fatal("proc %s missing RETURN, line %d" % (top, p.lineno(2)))
        else:
            if (len(g_code) == 0) or (get_instr(g_code[-1]) != 'RET'):
                g_code.append("RET  ; proc return")
                g_pc += 1
    g_ret = False
         
         
def p_if_then_statement(p):
    r'''if_then_statement : IF cond_expr THEN code_statement'''
    global g_pc, g_code, g_sym_list, g_do_stack, g_state_count
    es = pop_statement()
    #print("IFTHEN:", es)
    oldpc = g_pc
    mark_statement()
    collapse_left(p[2])
    label = new_label()
    g_code.append("XRA A  ; A = 0")
    g_code.append("CMP E  ; rel result")
    g_code.append("JZ %s  ; skip if" % label)
    g_pc += 5
    emit_code()
    size = g_pc - oldpc
    for sym in es:
        if isinstance(sym, CodeBlock):
            g_pc += sym.size
        sym.addr += size
        g_sym_list.append(sym)
        g_state_count += 1
    if p[4]:
        g_do_stack.pop()
        g_do_stack.append((label,))
    else:
        emit_label(label)
    if p[4]:
        p[0] = 2
    else:
        p[0] = 0
        
        
def p_else_statement(p):
    r'''else_statement : ELSE code_statement'''
    global g_pc, g_code, g_sym_list, g_state_count, g_do_stack
    es = pop_statement()
    label1 = new_label()
    label2 = g_sym_list.pop()
    #print("ELSE:", label1, label2, g_do_stack, p[2])
    g_code.append("JMP %s  ; skip else" % label1)
    g_pc += 3
    emit_label(label2.name)
    mark_statement()
    for sym in es:
        if isinstance(sym, CodeBlock):
            g_pc += sym.size
        sym.addr += 3
        g_sym_list.append(sym)
        g_state_count += 1
    if p[2] > 0:
        label2 = g_do_stack.pop()
        if p[2] > 1:
            g_do_stack.append(((label1, label2[0]),))
        else:
            g_do_stack.append((label1,))
    else:
        emit_label(label1)
    p[0] = 0
    
        
def p_goto_statement(p):
    r'''goto_statement : GO TO IDENT SEMICOLON'''
    global g_pc, g_code
    #print("GOTO:", p[3])
    mark_statement()
    g_code.append("JMP %s  ; GO TO" % p[3])
    g_pc += 3
    p[0] = 0
    
    
def p_call_statement(p):
    r'''call_statement : CALL IDENT SEMICOLON
                       | CALL IDENT LPARENS expr RPARENS SEMICOLON
                       | CALL IDENT LPARENS expr COMMA expr RPARENS SEMICOLON
                       | CALL IDENT LPARENS expr COMMA expr COMMA expr RPARENS SEMICOLON'''
    global g_pc, g_code
    proc = lookup_sym(p[2])
    if proc is None:
        fatal("unknown proc %s, line %d" % (p[2], p.lineno(1)))
    mark_statement()
    if len(p) == 4:
        if isinstance(proc, Procedure):
            if proc.num_args != 0:
                fatal("proc %s requires %d args, line %d" % (proc.name, proc.num_args, p.lineno(2)))
            ProcCall0(proc.name).collapse_left()
        else:
            if proc.size != 2:
                fatal("called variable %s must be address, line %d" % (proc.name, proc.num_args, p.lineno(2)))
            ProcCallAddr(proc.name).collapse_left()
        p[0] = 0
        return
    if (not isinstance(proc, Procedure)):
        fatal("ident %s not a procedure, line %d" % (proc.name, p.lineno(2)))
    if len(p) == 7:
        if proc.num_args != 1:
            fatal("proc %s requires %d args, line %d" % (proc.name, proc.num_args, p.lineno(2)))
        ProcCall1(proc.name, p[4]).collapse_left()
    elif len(p) == 9:
        if proc.num_args != 2:
            fatal("proc %s requires %d args, line %d" % (proc.name, proc.num_args, p.lineno(2)))
        ProcCall2(proc.name, p[4], p[6]).collapse_left()
    elif len(p) == 11:
        if proc.num_args != 3:
            fatal("proc %s requires %d args, line %d" % (proc.name, proc.num_args, p.lineno(2)))
        ProcCallExt(proc.name, [p[4], p[6], p[8]]).collapse_left()
    p[0] = 0
    
    
def p_return_statement(p):
    r'''return_statement : RETURN SEMICOLON
                         | RETURN expr SEMICOLON'''
    global g_pc, g_code, g_proc_stack, g_ret
    #print("RETURN")
    if len(g_proc_stack) == 0:
        fatal("return not allowed outside proc, line %d" % p.lineno(1))
    mark_statement()
    if len(p) == 4:
        proc = lookup_sym(g_proc_stack[-1])
        width = collapse_left(p[2])
        if width == 0:
            fatal("procedure %s does not return a value, line %d" % (p[2][0].name, p.lineno(1)))
        if width > proc.size:
            fatal("return overflow, line %d" % p.lineno(1))
        elif width < proc.size:
            g_code.append("MVI D,000H  ; zero pad MSB")
            g_pc += 2
    g_code.append("RET  ; proc return")
    g_pc += 1
    g_ret = True
    p[0] = 0
    
    
def p_assign_statement(p):
    r'''assign_statement : assign_list EQUAL expr SEMICOLON'''
    #print("ASSIGN:", p[1], p[3])
    varlist = p[1]
    for var in varlist:
        if isinstance(var, tuple):
            name = var[0]
        else:
            name = var
        sym = lookup_sym(name)
        if sym is None:
            fatal("unknown identifier %s, line %d" % (name, p.lineno(1)))
    mark_statement()
    width = collapse_left(p[3])
    n = 0
    pad = False
    for n in range(len(varlist)):
        var = varlist[n]
        if isinstance(var, tuple):
            pad = assign_array(var[0], var[1], width, pad)
        else:
            pad = assign_scalar(var, width, n == (len(varlist) - 1), pad)
    p[0] = 0
 
 
def assign_array(name, index, assignWidth, pad): 
    global g_code, g_pc
    sym = lookup_sym(name)
    elemWidth = sym.elem_size
    numElement = sym.size // elemWidth
    if isinstance(index, int):
        if (numElement != 0) and (index > (numElement - 1)):
            warning("array %s index %d overflow" % (name, index))
    if elemWidth < assignWidth:
        warning("BYTE array element overflow %s"  % name)
    if (elemWidth > assignWidth) and (not pad):
        pad = True
        g_code.append("MVI D,000H  ; zero pad elem MSB")
        g_pc += 2
    g_code.append("PUSH D  ; save left array");
    g_pc += 1
    indexWidth = collapse_left(index)
    if indexWidth == 1:
        g_code.append("MVI D,000H  ; zero pad index MSB");
        g_pc += 2
    if isinstance(sym, BasedArray):
        g_code.append("LHLD %s  ; store arr based" % sym.addr)
    else:
        if isinstance(sym, AtArray):
            if isinstance(sym.addr, int):
                name = "%05XH" % sym.addr
            else:
                name = sym.addr
        else:
            name = sym.name
        g_code.append("LXI H,%s  ; store arr" % name)
    g_pc += 3
    if elemWidth == 2:
        g_code.append("XCHG")
        g_code.append("DAD H  ; index << 1")
        g_pc += 2
    g_code.append("DAD D  ; arr offset")
    g_code.append("POP D  ; arr restore left")
    g_code.append("MOV M,E  ; arr assign from (D),C")
    g_pc += 3
    if elemWidth == 2:
        g_code.append("INX H")
        g_code.append("MOV M,D")
        g_pc += 2
    return pad
        
        
def assign_scalar(name, width, last, pad):
    global g_code, g_pc
    sym = lookup_sym(name)
    if isinstance(sym, BasedVariable):
        name = sym.addr
    else:
        name = sym.name
    if sym.size == 1:
        if width != 1:
            warning("BYTE variable overflow %s" % name)
        if isinstance(sym, BasedVariable):
            g_code.append("LHLD %s  ; assign based" % name)
        else:
            if isinstance(sym, AtVariable):
                if isinstance(sym.addr, int):
                    name = "%05XH" % sym.addr
                else:
                    name = sym.addr 
                if sym.value > 0:
                    name += " + %05XH" % sym.value
            g_code.append("LXI H,%s   ; assign" % name)
        g_code.append("MOV M,E    ; from E")
        g_pc += 4
    else:
        if (width == 1) and (not pad):
            pad = True
            g_code.append("MVI D,000H  ; zero pad MSB")
            g_pc += 2
        if isinstance(sym, BasedVariable):
            g_code.append("LHLD %s  ; assign based" % name)
            g_code.append("MOV M,E")
            g_code.append("INX H")
            g_code.append("MOV M,D  ; from D,E")
            g_pc += 6
        else:
            g_code.append("XCHG    ; from D,E")
            g_pc += 1
            if sym.name == "STACKPTR":
                g_code.append("SPHL  ; assign STACKPTR")
                g_pc += 1
            else:
                if isinstance(sym, AtVariable):
                    if isinstance(sym.addr, int):
                        name = "%05XH" % sym.addr
                    else:
                        name = sym.addr
                    if sym.value > 0:
                        name += " + %05XH" % sym.value
                g_code.append("SHLD %s ; assign" % name)
                g_pc += 3
            if not last:
                g_code.append("XCHG    ; restore D,E")
                g_pc += 1
    return pad
    
    
def p_assign_list(p):
    r'''assign_list : assign_list1 assign_var
                    | assign_var'''
    if len(p) == 2:
        p[0] = [p[1]]
    else:
        p[1].append(p[2])
        p[0] = p[1]
    
    
def p_assign_list1(p):
    '''assign_list1 : assign_list1 assign_var COMMA
                    | assign_var COMMA'''
    if len(p) == 3:
        p[0] = [p[1]]
    else:
        p[1].append(p[2])
        p[0] = p[1]
        
        
def p_assign_var(p):
    '''assign_var : IDENT LPARENS expr RPARENS
                  | IDENT'''
    if len(p) == 2:
        p[0] = p[1]
    else:
        p[0] = (p[1], p[3])
   
    
def p_expr(p):
    r'''expr : element_expr
             | arith_expr
             | logic_expr
             | rel_expr
             | LPARENS expr RPARENS'''
    if len(p) == 2:
        p[0] = p[1]
    else:
        p[0] = p[2]

   
def p_arith_expr(p):
    r'''arith_expr : add_expr
                   | sub_expr
                   | mul_expr
                   | div_expr
                   | mod_expr'''
    p[0] = p[1]
    
    
def p_logic_expr(p):
    r'''logic_expr : and_expr
                   | or_expr
                   | not_expr'''
    p[0] = p[1]
    
    
def p_rel_expr(p):
    r'''rel_expr : noteq_expr
                 | eq_expr
                 | lt_expr
                 | gt_expr
                 | lteq_expr
                 | gteq_expr'''
    p[0] = p[1]
    
    
def p_add_expr(p):
    '''add_expr : expr PLUS expr'''
    p[0] = (AdditionOp(p[1], p[3]),)
    #print("ADD: %s" % p[0])
    
    
def p_sub_expr(p):
    '''sub_expr : expr MINUS expr'''
    p[0] = (SubtractionOp(p[1], p[3]),)
    #print("SUB:", p[0])
    
    
def p_mul_expr(p):
    r'''mul_expr : expr ASTERIX expr'''
    p[0] = (MultiplicationOp(p[1], p[3]),)
    #print("MUL:", p[0])
    

def p_div_expr(p):
    r'''div_expr : expr DIV expr'''
    p[0] = (DivisionOp(p[1], p[3]),)
    #print("DIV:", p[0])
    

def p_mod_expr(p):
    r'''mod_expr : expr MOD expr'''
    p[0] = (ModOp(p[1], p[3]),)
    #print("MOD:", p[0])
    

def p_and_expr(p):
    r'''and_expr : expr AND expr'''
    p[0] = (AndOp(p[1], p[3]),)
    #print("AND:", p[0])
    

def p_or_expr(p):
    r'''or_expr : expr OR expr'''
    p[0] = (OrOp(p[1], p[3]),)
    #print("OR:", p[0])
    

def p_not_expr(p):
    r'''not_expr : NOT expr'''
    p[0] = (NotOp(p[2]),)
    #print("NOT:", p[0])
    

def p_eq_expr(p):
    r'''eq_expr : expr EQUAL expr'''
    p[0] = (EqualOp(p[1], p[3]),)
    #print("EQUAL:", p[0])
    

def p_noteq_expr(p):
    '''noteq_expr : expr NOTEQUAL expr'''
    p[0] = (NotEqualOp(p[1], p[3]),)
    #print("NOTEQ:", p[0])
    

def p_lt_expr(p):
    '''lt_expr : expr LESSTHAN expr'''
    p[0] = (LessThanOp(p[1], p[3]),)
    #print("LT:", p[0])
    

def p_lteq_expr(p):
    '''lteq_expr : expr LESSTHANEQUAL expr'''
    p[0] = (LessThanEqualOp(p[1], p[3]),)
    #print("LTEQ:", p[0])

    
def p_gt_expr(p):
    '''gt_expr : expr GREATERTHAN expr'''
    p[0] = (GreaterThanOp(p[1], p[3]),)
    #print("GT: %s" % p[0])
 
 
def p_gteq_expr(p):
    r'''gteq_expr : expr GREATERTHANEQUAL expr'''
    p[0] = (GreaterThanEqualOp(p[1], p[3]),)
    #print("GTEQ: %s" % p[0])
 
 
def p_bool_expr(p):
    r'''bool_expr : element_expr'''
    p[0] = (BoolOp(p[1]),)
    #print("BOOL %s" % p[0])
  
  
def p_element_expr(p):
    r'''element_expr : number
                     | IDENT
                     | IDENT LPARENS expr RPARENS
                     | proc_call2
                     | proc_call3
                     | reference
                     | reference LPARENS expr RPARENS
                     | inplace_assign
                     | struct_item'''
    if isinstance(p[1], (tuple, int)):
        p[0] = p[1]
    elif isinstance(p[1], Reference):
        if len(p) > 2:
            p[0] = (p[1], p[3])
        else:
            p[0] = (p[1], None)
    else:
        sym = lookup_sym(p[1])
        if not isinstance(sym, (Variable, Procedure)):
            fatal("unknown identifier %s, line %d" % (p[1], p.lineno(1)))
        if len(p) > 2:
            if isinstance(sym, Array):
                p[0] = (sym, p[3])
            elif isinstance(sym, Procedure):
                if sym.size == 0:
                    fatal("procedure %s does not return a value, line %d" % (sym.name, p.lineno(1)))
                p[0] = (ProcCall1(p[1], p[3]),)
        else:
            if isinstance(sym, Procedure):
                p[0] = (ProcCall0(p[1]),)
            else:
                p[0] = (sym,)
            
            
def p_proc_call2(p):
    r'''proc_call2 : IDENT LPARENS expr COMMA expr RPARENS'''
    p[0] = (ProcCall2(p[1], p[3], p[5]),)
    #print("PROC2: %s" % p[0])
    
    
def p_proc_call3(p):
    r'''proc_call3 : IDENT LPARENS expr COMMA expr COMMA expr RPARENS'''
    p[0] = (ProcCallExt(p[1], [p[3], p[5], p[7]]),)
    
    
def p_inplace_assign(p):
    r'''inplace_assign : IDENT ASSIGN expr
                       | LPARENS IDENT ASSIGN expr RPARENS'''
    #print("INASSIGN:", p[2], p[4])
    if len(p) == 4:
        name = p[1]
        expr = p[3]
    else:
        name = p[2]
        expr = p[4]
    sym = lookup_sym(name)
    if (not isinstance(sym, Variable)) or isinstance(sym, Array):
        fatal("inplace assign %d must be a scalar, line %d" % (name, p.lineno(2)))
    p[0] = (InplaceAssignOp(sym.name, expr),)
        
        
def p_reference(p):
    r'''reference : PERIOD IDENT
                  | PERIOD LPARENS ref_init_list RPARENS'''
    global g_anon_list
    if len(p) == 3:
        sym = lookup_sym(p[2])
        if sym is None:
            name = p[2]
        else:
            name = sym.name
    else:
        name = new_label()
        bdata = []
        for b in p[3]:
            if isinstance(b, str):
                for c in b:
                    bdata.append(ord(c))
            else:
                bdata.append(b)
        g_anon_list.append(Array(name, 0, len(bdata), bdata, 1))
    p[0] = Reference(name)
    
    
def p_ref_init_list(p):
    r'''ref_init_list : ref_init_list1 ref_data
                      | ref_data'''
    if len(p) == 2:
        p[0] = [p[1]]
    else:
        p[1].append(p[2])
        p[0] = p[1]
                   
                   
def p_ref_init_list1(p):
    r'''ref_init_list1 : ref_init_list1 ref_data COMMA
                       | ref_data COMMA'''
    if len(p) == 3:
        p[0] = [p[1]]
    else:
        p[1].append(p[2])
        p[0] = p[1]


def p_ref_data(p):
    r'''ref_data : number
                 | STRING'''
    p[0] = p[1]
    
    
def p_struct_item(p):
    r'''struct_item : IDENT PERIOD IDENT'''
    sym = lookup_sym(p[1])
    if not isinstance(sym, Struct):
        fatal("ident %s not a struct, line %d" % (p[1], p.lineno(1)))
    if not (p[3] in sym.value.keys()):
        fatal("item %s is not a member of struct %s, line %d" % (p[3], p[1], p.lineno(3)))
    p[0] = (sym, p[3])
    
    
def p_number(p):
    r'''number : DECNUMBER
               | HEXNUMBER
               | BINNUMBER'''
    p[0] = p[1]
    
    
def p_error(t):
    fatal("syntax error at %s(%s), line %d" % (t.value, t.type, t.lexer.lineno))
  
  
# token precedence rules for the parser
# tokens are listed from lowest to highest precedence   
precedence = (
    ('left', 'ASSIGN'),
    ('left', 'OR'),
    ('left', 'AND'),
    ('left', 'NOT'),
    ('left', 'GREATERTHAN', 'LESSTHAN', 'EQUAL', 'NOTEQUAL', 'GREATERTHANEQUAL', 'LESSTHANEQUAL'),
    ('left', 'PLUS', 'MINUS'),
    ('left', 'ASTERIX', 'DIV', 'MOD'),
    ('left', 'RPARENS', 'LPARENS'),
    ('left', 'IDENT'),
    ('left', 'STRING'),
    ('left', 'HEXNUMBER', 'DECNUMBER', 'BINNUMBER'),
)

parser = yacc.yacc()
   
   
class Operator(object): pass

class UnaryOp(Operator): 
    """Base class for operators with one argument"""
    
    def __init__(self, arg1):
        self.arg1 = arg1
        
    def __repr__(self):
        return "UnaryOp(%s)" % self.arg1
        
    def check_save(self, left):
        return (not left) and (not isinstance(self.arg1, int)) and isinstance(self.arg1[0], BinaryOp)
        
    def get_arg(self, left):
        global g_pc, g_code
        saveLeft = self.check_save(left)
        if saveLeft:
            g_code.append("PUSH D  ; save left unary")
            g_pc += 1
        return collapse_left(self.arg1)
        
    def exit(self, left):
        global g_pc, g_code
        saveLeft = self.check_save(left)
        if saveLeft:
            g_code.append("POP D  ; restore left unary")
            g_pc += 1
        
        
class BinaryOp(Operator):
    """Base class for operators with two arguments"""

    def __init__(self, arg1, arg2):
        self.arg1 = arg1
        self.arg2 = arg2
        
    def __repr__(self):
        return "BinaryOp(%s,%s)" % (self.arg1, self.arg2)
        
    def check_save(self):
        return (not isinstance(self.arg2, int)) and isinstance(self.arg2[0], Operator)
        
    def get_args(self):
        global g_pc, g_code
        leftWidth = collapse_left(self.arg1)
        saveLeft = self.check_save()
        if saveLeft:
            g_code.append("PUSH D ; save left binary")
            g_pc += 1
        rightWidth = collapse_right(self.arg2)
        if saveLeft:
            g_code.append("POP D  ; restore left binary")
            g_pc += 1
        return (leftWidth, rightWidth)
        
        
class ProcCall0(Operator):

    def __init__(self, name):
        self.name = name
        
    def __repr__(self):
        return "ProcCall0(%s)" % self.name
    
    def _collapse_common(self, proc, left):
        global g_pc, g_code
        g_code.append("CALL %s  ; proc call" % proc.name)
        g_pc += 3
        if (not left) and (proc.size > 0):
            g_code.append("MOV C,E  ; proc ret right to (B),C")
            g_pc += 1
            if proc.size == 2:
                g_code.append("MOV B,D")
                g_pc += 1
        return proc.size
    
    def collapse_left(self):
        sym = lookup_sym(self.name)
        if not isinstance(sym, Procedure):
            fatal("unknown procedure %s" % self.name)
        if sym.num_args != 0:
            fatal("procedure %s takes 0 arguments" % self.name)
        if isinstance(sym, BuiltinProcedure):
            return sym.handler(self, True)
        else:
            return self._collapse_common(sym, True)
        
    def collapse_right(self):
        sym = lookup_sym(self.name)
        if not isinstance(sym, Procedure):
            fatal("unknown procedure %s" % self.name)
        if sym.num_args != 0:
            fatal("procedure %s takes 0 arguments" % self.name)
        if isinstance(sym, BuiltinProcedure):
            return sym.handler(self, False)
        else:
            return self._collapse_common(sym, False)
            
class ProcCallAddr(Operator):

    def __init__(self, name):
        self.name = name
        
    def __repr__(self):
        return "ProcCallAddr(%s)" % self.name
    
    def _collapse_common(self, sym, left):
        global g_pc, g_code
        label = new_label()
        g_code.append("LXI H,%s ; proc ret" % label)
        g_code.append("PUSH H")
        g_code.append("LHLD %s  ; proc address" % sym.name)
        g_code.append("PCHL     ; proc call")
        g_pc += 8
        emit_label(label)
    
    def collapse_left(self):
        sym = lookup_sym(self.name)
        if not isinstance(sym, Variable):
            fatal("unknown variable %s" % self.name)
        self._collapse_common(sym, True)
        return 0
        
    def collapse_right(self):
        sym = lookup_sym(self.name)
        if not isinstance(sym, Variable):
            fatal("unknown variable %s" % self.name)
        self._collapse_common(sym, False)
        return 0
        
class ProcCall1(UnaryOp):

    def __init__(self, name, arg1):
        UnaryOp.__init__(self, arg1)
        self.name = name
        
    def _collapse_common(self, proc, left):
        global g_pc, g_code
        argWidth = self.get_arg(left)
        if argWidth > proc.arg_widths[0]:
            fatal("argument overflow for procedure %s arg 1" % proc.name)
        elif argWidth < proc.arg_widths[0]:
            g_code.append("MVI D,000H  ; zero pad MSB")
            g_pc += 2
        g_code.append("CALL %s  ; proc call" % proc.name)
        g_pc += 3
        if (not left) and (proc.size > 0):
            g_code.append("MOV C,E  ; proc ret right to (B),C")
            g_pc += 1
            if proc.size == 2:
                g_code.append("MOV B,D")
                g_pc += 1
        self.exit(left)
        return proc.size
        
    def collapse_left(self):
        sym = lookup_sym(self.name)
        if (not isinstance(sym, Procedure)):
            fatal("unknown procedure %s" % self.name)
        if sym.num_args != 1:
            fatal("procedure %s takes 1 argument" % self.name)
        if isinstance(sym, BuiltinProcedure):
            return sym.handler(self, True)
        else:
            return self._collapse_common(sym, True)
        
    def collapse_right(self):
        sym = lookup_sym(self.name)
        if (not isinstance(sym, Procedure)):
            fatal("unknown procedure %s" % self.name)
        if sym.num_args != 1:
            fatal("procedure %s takes 1 argument" % self.name)
        if isinstance(sym, BuiltinProcedure):
            return sym.handler(self, False)
        else:
            return self._collapse_common(sym, False)

class ProcCall2(BinaryOp):

    def __init__(self, name, arg1, arg2):
        BinaryOp.__init__(self, arg1, arg2)
        self.name = name
        
    def _collapse_common(self, proc, left):
        global g_pc, g_code
        (leftWidth, rightWidth) = self.get_args()
        if leftWidth > proc.arg_widths[0]:
            fatal("argument overflow for procedure %s arg 1" % proc.name)
        if rightWidth > proc.arg_widths[1]:
            fatal("argument overflow for procedure %s arg 2" % proc.name)
        if leftWidth < proc.arg_widths[0]:
            g_code.append("MVI D,000H  ; zero pad MSB")
            g_pc += 2
        if rightWidth < proc.arg_widths[1]:
            g_code.append("MVI B,000H  ; zero pad MSB")
            g_pc += 2
        g_code.append("CALL %s  ; proc call" % proc.name)
        g_pc += 3
        if (not left) and (proc.size > 0):
            g_code.append("MOV C,E  ; proc ret right to (B),C")
            g_pc += 1
            if proc.size == 2:
                g_code.append("MOV B,D")
                g_pc += 1
        return proc.size
        
    def collapse_left(self):
        sym = lookup_sym(self.name)
        if (not isinstance(sym, Procedure)):
            fatal("unknown procedure %s" % self.name)
        if sym.num_args != 2:
            fatal("procedure %s takes 2 arguments" % self.name)
        
        if isinstance(sym, BuiltinProcedure):
            return sym.handler(self, True)
        else:
            return self._collapse_common(sym, True)
        
    def collapse_right(self):
        sym = lookup_sym(self.name)
        if (not isinstance(sym, Procedure)):
            fatal("unknown procedure %s" % self.name)
        if sym.num_args != 2:
            fatal("procedure %s takes 2 arguments" % self.name)
        if isinstance(sym, BuiltinProcedure):
            return sym.handler(self, False)
        else:
            return self._collapse_common(sym, False)
            
class ProcCallExt(ProcCall2):

    def __init__(self, name, args):
        ProcCall2.__init__(self, name, args.pop(0), args.pop(0))
        self.ext_args = args
        
    def _collapse_common(self, proc, left):
        global g_pc, g_code
        for n in range(len(self.ext_args)):
            arg = self.ext_args[n]
            argWidth = collapse_left(arg)
            if argWidth > proc.arg_widths[n+2]:
                fatal("argument overflow for procedure %s arg" % proc.name)
            elif argWidth < proc.arg_widths[n+2]:
                g_code.append("MVI D,000H  ; zero pad MSB")
                g_pc += 2
            g_code.append("PUSH D  ; proc ext arg")
            g_pc += 1
        width = ProcCall2._collapse_common(self, proc, left)
        if not left:
            g_code.append("MOV C,E  ; proc ext right to (B),C")
            g_pc += 1
            if width == 2:
                g_code.append("MOV B,D")
                g_pc += 1
        for arg in self.ext_args:
            g_code.append("POP H  ; proc ext arg discard")
            g_pc += 1
        return proc.size
        
    def collapse_left(self):
        sym = lookup_sym(self.name)
        if (not isinstance(sym, Procedure)):
            fatal("unknown procedure %s" % self.name)
        numArg = len(self.ext_args) + 2
        if sym.num_args != numArg:
            fatal("procedure %s takes %d arguments" % (self.name, numArg))
        return self._collapse_common(sym, True)
        
    def collapse_right(self):
        sym = lookup_sym(self.name)
        if (not isinstance(sym, Procedure)):
            fatal("unknown procedure %s" % self.name)
        numArg = len(self.ext_args) + 2
        if sym.num_args != numArg:
            fatal("procedure %s takes %d arguments" % (self.name, numArg))
        return self._collapse_common(sym, False)
    
        
class AdditionOp(BinaryOp):

    def collapse_left(self):
        global g_pc, g_code
        (leftWidth, rightWidth) = self.get_args()
        maxWidth = max(leftWidth, rightWidth)
        if maxWidth == 1:
            g_code.append("MOV A,C")
            g_code.append("ADD E    ; + left")
            g_code.append("MOV E,A  ; result to E")
            g_pc += 3
        else:
            if rightWidth == 1:
                g_code.append("MVI B,000H  ; zero pad MSB")
                g_pc += 2
            elif leftWidth == 1:
                g_code.append("MVI D,000H  ; zero pad MSB")
                g_pc += 2
            g_code.append("XCHG   ; from D,E")
            g_code.append("DAD B  ; + left")
            g_code.append("XCHG   ; result to D,E")
            g_pc += 3
        return maxWidth
        
    def collapse_right(self):
        global g_pc, g_code
        (leftWidth, rightWidth) = self.get_args()
        maxWidth = max(leftWidth, rightWidth)
        if maxWidth == 1:
            g_code.append("MOV A,C")
            g_code.append("ADD E    ; + right")
            g_code.append("MOV C,A  ; result to C")
            g_pc += 3
        else:
            if rightWidth == 1:
                g_code.append("MVI B,000H  ; zero pad MSB")
                g_pc += 2
            elif leftWidth == 1:
                g_code.append("MVI D,000H  ; zero pad MSB")
                g_pc += 2
            g_code.append("XCHG     ; from D,E")
            g_code.append("DAD B    ; + right")
            g_code.append("MOV C,L  ; result to B,C")
            g_code.append("MOV B,H")
            g_pc += 4
        return maxWidth
        
class SubtractionOp(BinaryOp):
        
    def collapse_left(self):
        global g_pc, g_code
        (leftWidth, rightWidth) = self.get_args()
        maxWidth = max(leftWidth, rightWidth)
        if maxWidth == 1:
            g_code.append("MOV A,E")
            g_code.append("SUB C    ; - left")
            g_code.append("MOV E,A  ; result to E")
            g_pc += 3
        else:
            if rightWidth == 1:
                g_code.append("MVI B,000H  ; zero pad MSB")
                g_pc += 2
            elif leftWidth == 1:
                g_code.append("MVI D,000H  ; zero pad MSB")
                g_pc += 2
            g_code.append("MOV A,E")
            g_code.append("SUB C    ; - left")
            g_code.append("MOV E,A")
            g_code.append("MOV A,D")
            g_code.append("SBB B")
            g_code.append("MOV D,A  ; result to D,E")
            g_pc += 6
        return maxWidth
        
    def collapse_right(self):
        global g_pc, g_code
        (leftWidth, rightWidth) = self.get_args()
        maxWidth = max(leftWidth, rightWidth)
        if maxWidth == 1:
            g_code.append("MOV A,E")
            g_code.append("SUB C    ; - right")
            g_code.append("MOV C,A  ; result to C")
            g_pc += 3
        else:
            if rightWidth == 1:
                g_code.append("MVI B,000H  ; zero pad MSB")
                g_pc += 2
            elif leftWidth == 1:
                g_code.append("MVI D,000H  ; zero pad MSB")
                g_pc += 2
            g_code.append("MOV A,E")
            g_code.append("SUB C    ; - right")
            g_code.append("MOV C,A")
            g_code.append("MOV A,D")
            g_code.append("SBB B")
            g_code.append("MOV B,A  ; result to B,C")
            g_pc += 6
        return maxWidth
        
        
class MultiplicationOp(BinaryOp):
    """Generate code for * operator"""
    
    def _collapse_common(self, left, rightWidth):
        global g_pc, g_code
        label1 = new_label()
        label2 = new_label()
        if rightWidth == 1:
            g_code.append("MVI B,008H  ; * count")
        else:
            g_code.append("MVI A,010H  ; * count")
        g_code.append("LXI H,00000H  ; * init")
        g_pc += 5
        emit_label(label1)
        if rightWidth == 2:
            g_code.append("PUSH PSW  ; * save count")
            g_code.append("MOV A,B")
            g_code.append("RAR")
            g_code.append("MOV B,A")
            g_pc += 4
        g_code.append("MOV A,C")
        g_code.append("RAR")
        g_code.append("MOV C,A")
        g_code.append("JNC %s  ; * check bits of right arg" % label2)
        g_code.append("DAD D")
        g_pc += 7
        emit_label(label2)
        g_code.append("XCHG")
        g_code.append("DAD H")
        g_code.append("XCHG")
        g_pc += 3
        if rightWidth == 1:
            g_code.append("DCR B  ; check count")
            g_pc += 1
        else:
            g_code.append("POP PSW ;  * check count")
            g_code.append("DCR A")
            g_pc += 2
        g_code.append("JNZ %s ;  * more bits" % label1)
        g_pc += 3
        if left:
            g_code.append("XCHG  ; * result do D,E")
            g_pc += 1
        else:
            g_code.append("MOV C,L  ; * result to B,C")
            g_code.append("MOV B,H")
            g_pc += 2

    def collapse_left(self):
        global g_pc, g_code
        (leftWidth, rightWidth) = self.get_args()
        if leftWidth == 1:
            g_code.append("MVI D,000H  ; zero pad MSB")
            g_pc += 2
        self._collapse_common(True, rightWidth)
        return 2
        
    def collapse_right(self):
        global g_pc, g_code
        (leftWidth, rightWidth) = self.get_args()
        if leftWidth == 1:
            g_code.append("MVI D,000H  ; zero pad MSB")
            g_pc += 2
        self._collapse_common(False, rightWidth)
        return 2
        
        
class DivisionOp(BinaryOp):
    """Generate code for / operator"""
    
    def _collapse_common(self, left):
        global g_pc, g_code
        label1 = new_label()
        label2 = new_label()
        g_code.append("LXI H,00000H  ; / init")
        g_pc += 3
        emit_label(label1)
        g_code.append("MOV A,E")
        g_code.append("SUB C")
        g_code.append("MOV E,A")
        g_code.append("MOV A,D")
        g_code.append("SBB B")
        g_code.append("JC %s  ; / complete" % label2)
        g_code.append("MOV D,A")
        g_code.append("INX H")
        g_code.append("JMP %s  ; more /" % label1)
        g_pc += 13
        emit_label(label2)
        if left:
            g_code.append("XCHG  ; / result to D,E")
            g_pc += 1
        else:
            g_code.append("MOV C,L  ; / result to B,C")
            g_code.append("MOV B,H")
            g_pc += 2
        
    def collapse_left(self):
        global g_pc, g_code
        (leftWidth, rightWidth) = self.get_args()
        if rightWidth == 1:
            g_code.append("MVI B,000H  ; zero pad MSB")
            g_pc += 2
        if leftWidth == 1:
            g_code.append("MVI D,000H  ; zero pad MSB")
            g_pc += 2
        self._collapse_common(True)
        return 2
        
    def collapse_right(self):
        global g_pc, g_code
        (leftWidth, rightWidth) = self.get_args()
        if rightWidth == 1:
            g_code.append("MVI B,000H  ; zero pad MSB")
            g_pc += 2
        if leftWidth == 1:
            g_code.append("MVI D,000H  ; zero pad MSB")
            g_pc += 2
        self._collapse_common(False)
        return 2
        
class ModOp(BinaryOp):

    def _collapse_common(self, left):
        global g_pc, g_code
        label1 = new_label()
        emit_label(label1)
        g_code.append("MOV A,E")
        g_code.append("SUB C")
        g_code.append("MOV E,A")
        g_code.append("MOV A,D")
        g_code.append("SBB B")
        g_code.append("MOV D,A")
        g_code.append("JNC %s  ; more MOD" % label1)
        g_code.append("XCHG")
        g_code.append("DAD B")
        g_pc += 11
        if left:
            g_code.append("XCHG  ; MOD left to D,E")
            g_pc += 1
        else:
            g_code.append("MOV C,L")
            g_code.append("MOV B,H  ; MOD right to B,C")
            g_pc += 2
        
    def collapse_left(self):
        global g_pc, g_code
        (leftWidth, rightWidth) = self.get_args()
        if leftWidth == 1:
            g_code.append("MVI D,000H  ; zero pad MSB")
            g_pc += 2
        if rightWidth == 1:
            g_code.append("MVI B,000H  ; zero pad MSB")
            g_pc += 2
        self._collapse_common(True)
        return 2
        
    def collapse_right(self):
        global g_pc, g_code
        (leftWidth, rightWidth) = self.get_args()
        if leftWidth == 1:
            g_code.append("MVI D,000H  ; zero pad MSB")
            g_pc += 2
        if rightWidth == 1:
            g_code.append("MVI B,000H  ; zero pad MSB")
            g_pc += 2
        self._collapse_common(False)
        return 2
        
        
class AndOp(BinaryOp):

    def collapse_left(self):
        global g_pc, g_code
        (leftWidth, rightWidth) = self.get_args()
        maxWidth = max(leftWidth, rightWidth)
        if maxWidth == 1:
            g_code.append("MOV A,C")
            g_code.append("ANA E    ; & left")
            g_code.append("MOV E,A  ; result to E")
            g_pc += 3
        else:
            if rightWidth == 1:
                g_code.append("MVI B,000H  ; zero pad MSB")
                g_pc += 2
            elif leftWidth == 1:
                g_code.append("MVI D,000H  ; zero pad MSB")
                g_pc += 2
            g_code.append("MOV A,C")
            g_code.append("ANA E    ; & left")
            g_code.append("MOV E,A")
            g_code.append("MOV A,B")
            g_code.append("ANA D")
            g_code.append("MOV D,A  ; result to D,E")
            g_pc += 6
        return maxWidth
    
    def collapse_right(self):
        global g_pc, g_code
        (leftWidth, rightWidth) = self.get_args()
        maxWidth = max(leftWidth, rightWidth)
        if maxWidth == 1:
            g_code.append("MOV A,C")
            g_code.append("ANA E    ; & right")
            g_code.append("MOV C,A  ; result to C")
            g_pc += 3
        else:
            if rightWidth == 1:
                g_code.append("MVI B,000H  ; zero pad MSB")
                g_pc += 2
            elif leftWidth == 1:
                g_code.append("MVI D,000H  ; zero pad MSB")
                g_pc += 2
            g_code.append("MOV A,C")
            g_code.append("ANA E    ; & right")
            g_code.append("MOV C,A")
            g_code.append("MOV A,B")
            g_code.append("ANA D")
            g_code.append("MOV B,A  ; result to B,C")
            g_pc += 6
        return maxWidth
        
        
class OrOp(BinaryOp):

    def collapse_left(self):
        global g_pc, g_code
        (leftWidth, rightWidth) = self.get_args()
        maxWidth = max(leftWidth, rightWidth)
        if maxWidth == 1:
            g_code.append("MOV A,C")
            g_code.append("ORA E    ; | left")
            g_code.append("MOV E,A  ; result to E")
            g_pc += 3
        else:
            if rightWidth == 1:
                g_code.append("MVI B,000H  ; zero pad MSB")
                g_pc += 2
            elif leftWidth == 1:
                g_code.append("MVI D,000H  ; zero pad MSB")
                g_pc += 2
            g_code.append("MOV A,C")
            g_code.append("ORA E    ; | left")
            g_code.append("MOV E,A")
            g_code.append("MOV A,B")
            g_code.append("ORA D")
            g_code.append("MOV D,A  ; result to D,E")
            g_pc += 6
        return maxWidth
    
    def collapse_right(self):
        global g_pc, g_code
        (leftWidth, rightWidth) = self.get_args()
        maxWidth = max(leftWidth, rightWidth)
        if maxWidth == 1:
            g_code.append("MOV A,C")
            g_code.append("ORA E    ; | right")
            g_code.append("MOV C,A  ; result to C")
            g_pc += 3
        else:
            if rightWidth == 1:
                g_code.append("MVI B,000H  ; zero pad MSB")
                g_pc += 2
            elif leftWidth == 1:
                g_code.append("MVI D,000H  ; zero pad MSB")
                g_pc += 2
            g_code.append("MOV A,C")
            g_code.append("ORA E    ; | right")
            g_code.append("MOV C,A")
            g_code.append("MOV A,B")
            g_code.append("ORA D")
            g_code.append("MOV B,A  ; result to B,C")
            g_pc += 6
        return maxWidth
        
        
class NotOp(UnaryOp):

    def collapse_left(self):
        global g_pc, g_code
        width = self.get_arg(True)
        if width != 1:
            fatal("NOT argument BYTE overflow")
        g_code.append("MOV A,E")
        g_code.append("CMA      ; NOT left")
        g_code.append("ANI 001H")
        g_code.append("MOV E,A  ; result to E")
        g_pc += 5
        self.exit(False)
        return 1
    
    def collapse_right(self):
        global g_pc, g_code
        width = self.get_arg(False)
        if width != 1:
            fatal("NOT argument BYTE overflow")
        g_code.append("MOV A,E")
        g_code.append("CMA      ; NOT right")
        g_code.append("ANI 001H")
        g_code.append("MOV C,A  ; result to C")
        g_pc += 5
        self.exit(False)
        return width
        
        
class EqualOp(BinaryOp):
    
    def _collapse_common(self, left):
        global g_pc, g_code, g_sym_list
        label1 = new_label()
        label2 = new_label()
        (leftWidth, rightWidth) = self.get_args()
        maxWidth = max(leftWidth, rightWidth)
        if maxWidth == 1:
            g_code.append("MOV A,C")
            g_code.append("CMP E ; =")
            g_code.append("JNZ %s ; !=" % label1)
            g_pc += 5
        else:
            if leftWidth == 1:
                g_code.append("MVI D,000H  ; zero pad MSB")
                g_pc += 2
            elif rightWidth == 1:
                g_code.append("MVI B,000H  ; zero pad MSB")
                g_pc += 2
            g_code.append("MOV A,C")
            g_code.append("CMP E  ; =")
            g_code.append("JNZ %s ; !=" % label1)
            g_code.append("MOV A,B")
            g_code.append("CMP D  ; =")
            g_code.append("JNZ %s ; !=" % label1)
            g_pc += 10
        if left:
            g_code.append("MVI E,001H  ; rel true left")
        else:
            g_code.append("MVI C,001H  ; rel true right")
        g_code.append("JMP %s" % label2)
        g_pc += 5
        emit_label(label1)
        if left:
            g_code.append("MVI E,000H  ; rel false left")
        else:
            g_code.append("MVI C,000H  ; rel false right")
        g_pc += 2
        emit_label(label2)
        
    def collapse_left(self):
        self._collapse_common(True)
        return 1
        
    def collapse_right(self):
        self._collapse_common(False)
        return 1
        
        
class NotEqualOp(BinaryOp):
    
    def _collapse_common(self, left):
        global g_pc, g_code, g_sym_list
        label1 = new_label()
        label2 = new_label()
        (leftWidth, rightWidth) = self.get_args()
        maxWidth = max(leftWidth, rightWidth)
        if maxWidth == 1:
            g_code.append("MOV A,C")
            g_code.append("CMP E ; <>")
            g_code.append("JZ %s ; =" % label1)
            g_pc += 5
        else:
            label3 = new_label()
            label4 = new_label()
            if leftWidth == 1:
                g_code.append("MVI D,000H  ; zero pad MSB")
                g_pc += 2
            elif rightWidth == 1:
                g_code.append("MVI B,000H  ; zero pad MSB")
                g_pc += 2
            g_code.append("MOV A,C")
            g_code.append("CMP E  ; <>")
            g_code.append("JZ %s  ; =" % label3)
            g_code.append("JMP %s ; !=" % label4)
            g_pc += 8
            emit_label(label3)
            g_code.append("MOV A,B")
            g_code.append("CMP D  ; <>")
            g_code.append("JZ %s ; =" % label1)
            g_pc += 5
            emit_label(label4)
        if left:
            g_code.append("MVI E,001H  ; rel true left")
        else:
            g_code.append("MVI C,001H  ; rel true right")
        g_code.append("JMP %s" % label2)
        g_pc += 5
        emit_label(label1)
        if left:
            g_code.append("MVI E,000H  ; rel false left")
        else:
            g_code.append("MVI C,000H  ; rel false right")
        g_pc += 2
        emit_label(label2)
        
    def collapse_left(self):
        self._collapse_common(True)
        return 1
        
    def collapse_right(self):
        self._collapse_common(False)
        return 1
        
        
class LessThanOp(BinaryOp):

    def _collapse_common(self, left):
        global g_pc, g_code, g_sym_list
        label1 = new_label()
        label2 = new_label()
        (leftWidth, rightWidth) = self.get_args()
        maxWidth = max(leftWidth, rightWidth)
        if maxWidth == 1:
            g_code.append("MOV A,C")
            g_code.append("CMP E  ; < ")
            g_code.append("JC %s" % label1)
            g_code.append("JZ %s" % label1)
            g_pc += 8
        else:
            label3 = new_label()
            label4 = new_label()
            if leftWidth == 1:
                g_code.append("MVI D,000H  ; zero pad MSB")
                g_pc += 2
            elif rightWidth == 1:
                g_code.append("MVI B,000H  ; zero pad MSB")
                g_pc += 2
            g_code.append("MOV A,D")
            g_code.append("CMP B  ; <")
            g_code.append("JZ %s   ; =" % label3)
            g_code.append("JNC %s  ; >" % label1)
            g_code.append("JMP %s  ; <" % label4)
            g_pc += 11
            emit_label(label3)
            g_code.append("MOV A,E")
            g_code.append("CMP C  ; <")
            g_code.append("JNC %s ; >=" % label1)
            g_pc += 5
            emit_label(label4)
        if left:
            g_code.append("MVI E,001H  ; rel true left")
        else:
            g_code.append("MVI C,001H  ; rel true right")
        g_code.append("JMP %s" % label2)
        g_pc += 5
        emit_label(label1)
        if left:
            g_code.append("MVI E,000H  ; rel false left")
        else:
            g_code.append("MVI C,000H  ; rel false right")
        g_pc += 2
        emit_label(label2)
        
    def collapse_left(self):
        self._collapse_common(True)
        return 1
        
    def collapse_right(self):
        self._collapse_common(False)
        return 1
        
        
class GreaterThanOp(BinaryOp):

    def _collapse_common(self, left):
        global g_pc, g_code, g_sym_list
        label1 = new_label()
        label2 = new_label()
        (leftWidth, rightWidth) = self.get_args()
        maxWidth = max(leftWidth, rightWidth)
        if maxWidth == 1:
            g_code.append("MOV A,C")
            g_code.append("CMP E  ; > ")
            g_code.append("JNC %s" % label1)
            g_pc += 5
        else:
            label3 = new_label()
            label4 = new_label()
            if leftWidth == 1:
                g_code.append("MVI D,000H  ; zero pad MSB")
                g_pc += 2
            elif rightWidth == 1:
                g_code.append("MVI B,000H  ; zero pad MSB")
                g_pc += 2
            g_code.append("MOV A,D")
            g_code.append("CMP B   ; >")
            g_code.append("JC %s   ; <" % label1)
            g_code.append("JZ %s   ; =" % label3)
            g_code.append("JMP %s  ; >" % label4)
            g_pc += 11
            emit_label(label3)
            g_code.append("MOV A,E")
            g_code.append("CMP C  ; >")
            g_code.append("JC %s  ; <" % label1)
            g_code.append("JZ %s  ; =" % label1)
            g_pc += 8
            emit_label(label4)
        if left:
            g_code.append("MVI E,001H  ; rel true left")
        else:
            g_code.append("MVI C,001H  ; rel true right")
        g_code.append("JMP %s" % label2)
        g_pc += 5
        emit_label(label1)
        if left:
            g_code.append("MVI E,000H  ; rel false left")
        else:
            g_code.append("MVI C,000H  ; rel false right")
        g_pc += 2
        emit_label(label2)
        
    def collapse_left(self):
        self._collapse_common(True)
        return 1
        
    def collapse_right(self):
        self._collapse_common(False)
        return 1
        
        
class LessThanEqualOp(BinaryOp):

    def _collapse_common(self, left):
        global g_pc, g_code, g_sym_list
        label1 = new_label()
        label2 = new_label()
        label3 = new_label()
        (leftWidth, rightWidth) = self.get_args()
        maxWidth = max(leftWidth, rightWidth)
        if maxWidth == 1:
            g_code.append("MOV A,C")
            g_code.append("CMP E   ; <=")
            g_code.append("JC %s" % label1)
            g_pc += 5
            emit_label(label3)
        else:
            label3 = new_label()
            label4 = new_label()
            if leftWidth == 1:
                g_code.append("MVI D,000H  ; zero pad MSB")
                g_pc += 2
            elif rightWidth == 1:
                g_code.append("MVI B,000H  ; zero pad MSB")
                g_pc += 2
            g_code.append("MOV A,D")
            g_code.append("CMP B  ; <=")
            g_code.append("JZ %s ; =" % label3)
            g_code.append("JNC %s  ; >" % label1)
            g_code.append("JMP %s  ; <" % label4)
            g_pc += 11
            emit_label(label3)
            g_code.append("MOV A,E")
            g_code.append("CMP C  ; <=")
            g_code.append("JZ %s  ; =" % label4)
            g_code.append("JNC %s  ; >" % label1)
            g_pc += 8
            emit_label(label4)
        if left:
            g_code.append("MVI E,001H  ; rel true left")
        else:
            g_code.append("MVI C,001H  ; rel true right")
        g_code.append("JMP %s" % label2)
        g_pc += 5
        emit_label(label1)
        if left:
            g_code.append("MVI E,000H  ; rel false left")
        else:
            g_code.append("MVI C,000H  ; rel false right")
        g_pc += 2
        emit_label(label2)
        
    def collapse_left(self):
        self._collapse_common(True)
        return 1
        
    def collapse_right(self):
        self._collapse_common(False)
        return 1
        
        
class GreaterThanEqualOp(BinaryOp):

    def _collapse_common(self, left):
        global g_pc, g_code, g_sym_list
        label1 = new_label()
        label2 = new_label()
        (leftWidth, rightWidth) = self.get_args()
        maxWidth = max(leftWidth, rightWidth)
        if maxWidth == 1:
            g_code.append("MOV A,C")
            g_code.append("CMP E  ; >= ")
            g_code.append("JZ %s   ; = " % label3)
            g_code.append("JNC %s" % label1)
            g_pc += 8
        else:
            label3 = new_label()
            label4 = new_label()
            if leftWidth == 1:
                g_code.append("MVI D,000H  ; zero pad MSB")
                g_pc += 2
            elif rightWidth == 1:
                g_code.append("MVI B,000H  ; zero pad MSB")
                g_pc += 2
            g_code.append("MOV A,D")
            g_code.append("CMP B  ; >=")
            g_code.append("JZ %s  ; =" % label3)
            g_code.append("JC %s  ; <" % label1)
            g_code.append("JMP %s ; >" % label4)
            g_pc += 11
            emit_label(label3)
            g_code.append("MOV A,E")
            g_code.append("CMP C  ; >=")
            g_code.append("JC %s  ; <" % label1)
            g_pc += 5
            emit_label(label4)
        if left:
            g_code.append("MVI E,001H  ; rel true left")
        else:
            g_code.append("MVI C,001H  ; rel true right")
        g_code.append("JMP %s" % label2)
        g_pc += 5
        emit_label(label1)
        if left:
            g_code.append("MVI E,000H  ; rel false left")
        else:
            g_code.append("MVI C,000H  ; rel false right")
        g_pc += 2
        emit_label(label2)
        
    def collapse_left(self):
        self._collapse_common(True)
        return 1
        
    def collapse_right(self):
        self._collapse_common(False)
        return 1
        
        
class BoolOp(UnaryOp):

    def _collapse_common(self, left):
        global g_pc, g_code
        width = self.get_arg(left)
        if width != 1:
            fatal("bool expression BYTE overflow")
        g_code.append("MOV A,E")
        g_code.append("ANI 001H  ; bool")
        if left:
            g_code.append("MOV E,A   ; left to E")
        else:
            g_code.append("MOV C,A   ; right to C")
        g_pc += 4
        self.exit(left)
    
    def collapse_left(self):
        self._collapse_common(True)
        return 1
        
    def collapse_right(self):
        self._collapse_common(False)
        return 1
        
        
class InplaceAssignOp(UnaryOp):

    def __init__(self, name, arg):
        UnaryOp.__init__(self, arg)
        self.name = name
        
    def _collapse_common(self, left):
        global g_code, g_pc
        sym = lookup_sym(self.name)
        width = self.get_arg(left)
        assign_scalar(self.name, width, False, False)
        if not left:
            g_code.append("MOV C,E  ; inp assign right")
            g_pc += 1
            if width == 2:
                g_code.append("MOV D,B")
                g_pc += 1
        self.exit(left)
        return sym.size
        
    def collapse_left(self):
        return self._collapse_common(True)
        
    def collapse_right(self):
        return self._collapse_common(False)
    
    
def collapse_left(node):
    if isinstance(node, int):
        return collapse_const_left(node)
    elif isinstance(node[0], Variable):
        return collapse_variable_left(node)
    elif isinstance(node[0], Operator):
        return node[0].collapse_left()
 
 
def collapse_right(node):
    if isinstance(node, int):
        return collapse_const_right(node)
    elif isinstance(node[0], Variable):
        return collapse_variable_right(node)
    elif isinstance(node[0], Operator):
        return node[0].collapse_right()
   
   
def collapse_const_left(node):
    global g_pc, g_code
    if node < 0x100:
        g_code.append("MVI E,%03XH  ; load const left" % node)
        g_pc += 2
        width = 1
    elif node < 0x10000:
        g_code.append("LXI D,%05XH  ; load const left" % node)
        g_pc += 3
        width = 2
    else:
        fatal("constant too large %d" % node)
    return width
        
        
def collapse_const_right(node):
    global g_pc, g_code
    if node < 0x100:
        g_code.append("MVI C,%03XH  ; load const right" % node)
        g_pc += 2
        width = 1
    elif node < 0x10000:
        g_code.append("LXI B,%05XH  ; load const right" % node)
        g_pc += 3
        width = 2
    else:
        fatal("constant too large %d" % node)
    return width
       
       
def collapse_variable_left(node):
    global g_pc, g_code, sg_flag_names
    if isinstance(node[0], Array):
        width = collapse_array_left(node)
    elif isinstance(node[0], Reference):
        width = collapse_reference_left(node)
    elif isinstance(node[0], Struct):
        width = collapse_struct_left(node)
    else:
        node = node[0]
        width = node.size
        if isinstance(node, BasedVariable):
            name = node.addr
        else:
            name = node.name
        if width == 1:
            if node.name in g_flag_names:
                return collapse_flags_left(node)
            if isinstance(node, BasedVariable):
                g_code.append("LHLD %s  ; load based left" % name)
            else:
                if isinstance(node, AtVariable):
                    if isinstance(node.addr, int):
                        name = "%05XH" % node.addr
                    else:
                        name = node.addr
                    if node.value > 0:
                        name += " + %05XH" % node.value
                g_code.append("LXI H,%s  ; load var left" % name)
            g_code.append("MOV E,M   ; to E")
            g_pc += 4
        else:
            if node.name == "STACKPTR":
                g_code.append("LXI H,00000H  ; load STACKPTR left")
                g_code.append("DAD SP")
                g_code.append("XCHG  ; to D,E")
                g_pc += 5
            elif isinstance(node, BasedVariable):
                g_code.append("LHLD %s  ; load based left" % name)
                g_code.append("MOV E,M")
                g_code.append("INX H")
                g_code.append("MOV D,M  ; to D,E")
                g_pc += 6
            else:
                if isinstance(node, AtVariable):
                    if isinstance(node.addr, int):
                        name = "%05XH" % node.addr
                    else:
                        name = node.addr 
                    if node.value > 0:
                        name += " + %05XH" % node.value
                g_code.append("LHLD %s ; load var left" % name)
                g_code.append("XCHG    ; to D,E")
                g_pc += 4
    return width
    
    
def collapse_array_left(node):
    global g_pc, g_code
    index = node[1]
    node = node[0]
    elemWidth = node.elem_size
    if isinstance(index, int):
        numElement = node.size // elemWidth
        if (numElement != 0) and (index > (numElement - 1)):
            warning("array %s index %d overflow" % (node.name, index))
    indexWidth = collapse_left(index)
    if indexWidth == 1:
        g_code.append("MVI D,000H  ; zero pad index MSB")
        g_pc += 2
    if isinstance(node, BasedArray):
        g_code.append("LHLD %s  ; load arr based left" % node.addr)
    else:
        if isinstance(node, AtArray):
            if isinstance(node.addr, int):
                name = "%05XH" % node.addr
            else:
                name = node.addr
        else:
            name = node.name
        g_code.append("LXI H,%s  ; load arr left" % name)
    g_pc += 3 
    if elemWidth == 2:
        g_code.append("XCHG")
        g_code.append("DAD H  ; index << 1")
        g_pc += 2
    g_code.append("DAD D    ; arr offset")
    g_code.append("MOV E,M  ; arr element to (D),E")
    g_pc += 2
    if elemWidth == 2:
        g_code.append("INX H")
        g_code.append("MOV D,M")
        g_pc += 2
    return elemWidth
 
 
def collapse_reference_left(node):
    global g_pc, g_code
    index = node[1]
    node = node[0]
    sym = lookup_sym(node.name)
    if isinstance(sym, (AtArray, AtVariable)):
        name = "%05XH" % sym.addr
    else:
        name = node.name
    if index is None:
        if isinstance(sym, BasedArray):
            sym = lookup_sym(sym.addr)
            g_code.append("LHLD %s  ; load ref right" % sym.name)
        else:
            g_code.append("LXI D,%s  ; load ref left" % name)
        g_pc += 3
    else:
        elemWidth = sym.elem_size
        indexWidth = collapse_left(index)
        if indexWidth == 1:
            g_code.append("MVI D,000H  ; zero pad MSB")
            g_pc += 2
        if isinstance(sym, BasedArray):
            sym = lookup_sym(sym.addr)
            g_code.append("LHLD %s  ; load ref right" % sym.name)
        else:
            g_code.append("LXI H,%s  ; load ref left" % name)
        g_pc += 3 
        if elemWidth == 2:
            g_code.append("XCHG")
            g_code.append("DAD H  ; index << 1")
            g_pc += 2
        g_code.append("DAD D    ; ref offset")
        g_code.append("XCHG     ; to D,E")
        g_pc += 2
    return 2
  
  
def collapse_struct_left(node):
    global g_pc, g_code
    item = node[1]
    node = node[0]
    desc = node.value[item]
    itemWidth = desc[1]
    g_code.append("LHLD %s  ; load struct based left" % node.addr)
    g_code.append("LXI D,%05XH" % desc[0])
    g_code.append("DAD D     ; struct offset")
    g_code.append("MOV E,M   ; to (D),E")
    g_pc += 8
    if itemWidth == 2:
        g_code.append("INX H")
        g_code.append("MOV D,M")
        g_pc += 2
    return itemWidth
    
    
def collapse_flags_left(node):
    global g_pc, g_code
    #print("FLAGS", node.name)
    label1 = new_label()
    label2 = new_label()
    if node.name == "ZERO":
        g_code.append("JNZ %s  ; ZERO" % label1)
    elif node.name == "CARRY":
        g_code.append("JNC %s  ; CARRY" % label1)
    elif node.name == "PARITY":
        g_code.append("JPO %s  ; PARITY" % label1)
    elif node.name == "SIGN":
        g_code.append("JP %s  ; SIGN" % label1)
    else:
        fatal("flag %s not supported" % node.name)
    g_code.append("MVI E,001H  ; flags true left")
    g_code.append("JMP %s" % label2)
    g_pc += 8
    emit_label(label1)
    g_code.append("MVI E,000H  ; flags false left")
    g_pc += 2
    emit_label(label2)
    return 1
     
     
def collapse_variable_right(node):
    global g_pc, g_code, g_flag_names
    if isinstance(node[0], Array):
        width = collapse_array_right(node)
    elif isinstance(node[0], Reference):
        width = collapse_reference_right(node)
    elif isinstance(node[0], Struct):
        width = collapse_struct_right(node)
    else:
        node = node[0]
        width = node.size
        if isinstance(node, BasedVariable):
            name = node.addr
        else:
            name = node.name
        if width == 1:
            if node.name in g_flag_names:
                return collapse_flags_right(node)
            if isinstance(node, BasedVariable):
                g_code.append("LHLD %s  ; load based right")
            else:
                if isinstance(node, AtVariable):
                    if isinstance(node.addr, int):
                        name = "%05XH" % node.addr
                    else:
                        name = node.addr
                    if node.value > 0:
                        name += " + %05XH" % node.value
                g_code.append("LXI H,%s  ; load var right" % name)
            g_code.append("MOV C,M   ; to C")
            g_pc += 4
        else:
            if node.name == "STACKPTR":
                g_code.append("LXI H,00000H  ; load STACKPTR")
                g_code.append("DAD SP")
                g_code.append("MOV C,L")
                g_code.append("MOV B,H ; to B,C")
                g_pc += 6
            elif isinstance(node, BasedVariable):
                g_code.append("LHLD %s  ; load based right" % name)
                g_code.append("MOV C,M")
                g_code.append("INX H")
                g_code.append("MOV B,M  ; to B,C")
                g_pc += 6
            else:
                if isinstance(node, AtVariable):
                    if isinstance(node.addr, int):
                        name = "%05XH" % node.addr
                    else:
                        name = node.addr 
                    if node.value > 0:
                        name += " + %05XH" % node.value
                g_code.append("LHLD %s ; load var right" % name)
                g_code.append("MOV C,L")
                g_code.append("MOV B,H ; to B,C")
                g_pc += 5
    return width
  
  
def collapse_array_right(node): 
    global g_pc, g_code
    index = node[1]
    node = node[0]
    elemWidth = node.elem_size
    if isinstance(index, int):
        numElement = node.size // elemWidth
        if (numElement != 0) and (index > (numElement - 1)):
            warning("array %s index %d overflow" % (node.name, index))
    g_code.append("PUSH D  ; save left array")
    g_pc += 1
    indexWidth = collapse_left(index)
    if indexWidth == 1:
        g_code.append("MVI D,000H  ; zero pad index MSB")
        g_pc += 2
    if isinstance(node, BasedArray):
        g_code.append("LHLD %s  ; load arr based right" % node.addr)
    else:
        if isinstance(node, AtArray):
            if isinstance(node.addr, int):
                name = "%05XH" % node.addr
            else:
                name = node.addr
        else:
            name = node.name
        g_code.append("LXI H,%s  ; load arr right" % name)
    g_pc += 3 
    if elemWidth == 2:
        g_code.append("XCHG")
        g_code.append("DAD H  ; index << 1")
        g_pc += 2
    g_code.append("DAD D    ; arr offset")
    g_code.append("MOV C,M  ; arr element to (B),C")
    g_pc += 2
    if elemWidth == 2:
        g_code.append("INX H")
        g_code.append("MOV B,M")
        g_pc += 2
    g_code.append("POP D  ; restore left array")
    g_pc += 1
    return elemWidth
    
    
def collapse_reference_right(node):
    global g_pc, g_code
    index = node[1]
    node = node[0]
    sym = lookup_sym(node.name)
    if isinstance(sym, (AtArray, AtVariable)):
        name = "%05XH" % sym.addr
    else:
        name = node.name
    if index is None:
        if isinstance(sym, BasedArray):
            sym = lookup_sym(sym.addr)
            g_code.append("LHLD %s  ; load ref right" % sym.name)
        else:
            g_code.append("LXI B,%s  ; load ref right" % name)
        g_pc += 3
    else:
        elemWidth = sym.elem_size
        g_code.append("PUSH D  ; save left ref")
        g_pc += 1
        indexWidth = collapse_left(index)
        if indexWidth == 1:
            g_code.append("MVI D,000H  ; zero pad MSB")
            g_pc += 2
        if isinstance(sym, BasedArray):
            sym = lookup_sym(sym.addr)
            g_code.append("LHLD %s  ; load ref right" % sym.name)
        else:
            g_code.append("LXI H,%s  ; load ref right" % name)
        g_pc += 3 
        if elemWidth == 2:
            g_code.append("XCHG")
            g_code.append("DAD H  ; index << 1")
            g_pc += 2
        g_code.append("DAD D    ; ref offset")
        g_code.append("MOV C,L  ; to B,C")
        g_code.append("MOV B,H")
        g_code.append("POP D  ; restore left ref")
        g_pc += 4
    return 2
    

def collapse_struct_right(node):
    global g_pc, g_code
    item = node[1]
    node = node[0]
    desc = node.value[item]
    itemWidth = desc[1]
    g_code.append("LHLD %s  ; load struct based right" % node.addr)
    g_code.append("LXI B,%05XH" % desc[0])
    g_code.append("DAD B     ; struct offset")
    g_code.append("MOV C,M   ; to (B),C")
    g_pc += 8
    if itemWidth == 2:
        g_code.append("INX H")
        g_code.append("MOV B,M")
        g_pc += 2
    return itemWidth
    
    
def collapse_flags_right(node):
    global g_pc, g_code
    #print("FLAGS", node.name)
    label1 = new_label()
    label2 = new_label()
    if node.name == "ZERO":
        g_code.append("JNZ %s  ; ZERO" % label1)
    elif node.name == "CARRY":
        g_code.append("JNC %s  ; CARRY" % label1)
    elif node.name == "PARITY":
        g_code.append("JPO %s  ; PARITY" % label1)
    elif node.name == "SIGN":
        g_code.append("JP %s  ; SIGN" % label1)
    else:
        fatal("flag %s not supported" % node.name)
    g_code.append("MVI C,001H  ; flags true right")
    g_code.append("JMP %s" % label2)
    g_pc += 8
    emit_label(label1)
    g_code.append("MVI C,000H  ; flags false right")
    g_pc += 2
    emit_label(label2)
    return 1
    
    
def builtin_length(node, left):
    """Generate code for builtin LENGTH() procedure"""
    global g_code, g_pc
    #print("LENGTH: %s" % node)
    sym = node.arg1[0]
    if not isinstance(sym, Array):
        fatal("LENGTH argument %s not an array" % sym.name)
    numElem = sym.size // sym.elem_size
    if numElem > 0xff:
        width = 2
    else:
        width = 1
    if width == 1:
        if left:
            g_code.append("MVI E,%03XH  ; LENGTH low left" % numElem)
        else:
            g_code.append("MVI C,%03XH  ; LENGTH low right" % numElem)
        g_pc += 2
    else:
        if left:
            g_code.append("LXI D,%05XH  ; LENGTH high left" % numElem)
        else:
            g_code.append("LXI B,%05XH  ; LENGTH high right" % numElem)
    return width
    
    
def builtin_last(node, left):
    """Generate code for builtin LAST() procedure"""
    global g_code, g_pc
    #print("LAST:", node)
    sym = node.arg1[0]
    if not isinstance(sym, Array):
        fatal("LAST argument %s not an array" % sym.name)
    if sym.size == 0:
        fatal("LAST argument array %s is zero size" % sym.name)
    index = (sym.size // sym.elem_size) - 1
    if index > 0xff:
        width = 2
    else:
        width = 1
    if width == 1:
        if left:
            g_code.append("MVI E,%03XH  ; LAST low left" % index)
        else:
            g_code.append("MVI C,%03XH  ; LAST low right" % index)
        g_pc += 2
    else:
        if left:
            g_code.append("LXI D,%05XH  ; LAST high left" % index)
        else:
            g_code.append("LXI B,%05XH  ; LAST high right" % index)
        g_pc += 3
    return width
    
    
def builtin_low(node, left):
    """Generate code for builtin LOW() procedure"""
    global g_pc, g_code
    #print("LOW: %s" % node)
    width = node.get_arg(left)
    if width != 2:
        fatal("LOW argument not ADDRESS");
    if not left:
        g_code.append("MOV C,E  ; LOW right")
        g_pc += 1
    node.exit(left)
    return 1
    
    
def builtin_high(node, left):
    """Generate code for builtin HIGH() procedure"""
    global g_pc, g_code
    #print("HIGH: %s" % node)
    width = node.get_arg(left)
    if width != 2:
        fatal("HIGH argument not ADDRESS");
    if left:
        g_code.append("MOV E,D  ; HIGH left")
    else:
        g_code.append("MOV C,D  ; HIGH right")
    g_pc += 1
    node.exit(left)
    return 1
    
    
def builtin_double(node, left):
    """Generate code for builtin DOUBLE() procedure"""
    global g_pc, g_code
    width = node.get_arg(left)
    if width != 1:
        fatal("DOUBLE argument not BYTE");
    if left:
        g_code.append("MVI D,000H  ; DOUBLE left")
        g_pc += 2
    else:
        g_code.append("MOV C,E")
        g_code.append("MVI B,000H  ; DOUBLE right")
        g_pc += 3
    node.exit(left)
    return 2
    
    
def builtin_shr(node, left):
    """Generate code for builtin SHR() procedure"""
    global g_pc, g_code
    #print("SHR:", left)
    (leftWidth, rightWidth) = node.get_args()
    if rightWidth != 1:
        warning("SHR arg 2 overflow")
    label1 = new_label()
    emit_label(label1)
    g_code.append("ORA A  ; clear carry")
    g_pc += 1
    if leftWidth == 2:
        g_code.append("MOV A,D")
        g_code.append("RAR")
        g_code.append("MOV D,A")
        g_pc += 3
    g_code.append("MOV A,E")
    g_code.append("RAR  ; SHR")
    g_code.append("MOV E,A")
    g_code.append("DCR C")
    g_code.append("JNZ %s  ; more SHR" % label1)
    g_pc += 7
    if not left:
        g_code.append("MOV C,E  ; SHR right")
        g_pc += 1
        if leftWidth == 2:
            g_code.append("MOV D,B")
            g_pc += 1
    return leftWidth
    
    
def builtin_shl(node, left):
    """Generate code for builtin SHL() procedure"""
    global g_pc, g_code
    #print("SHL:", left)
    (leftWidth, rightWidth) = node.get_args()
    if rightWidth != 1:
        warning("SHL arg 2 overflow")
    label1 = new_label()
    emit_label(label1)
    g_code.append("ORA A  ; clear carry")
    g_code.append("MOV A,E")
    g_code.append("RAL  ; SHL")
    g_code.append("MOV E,A")
    g_pc += 4
    if leftWidth == 2:
        g_code.append("MOV A,D")
        g_code.append("RAL")
        g_code.append("MOV D,A")
        g_pc += 3
    g_code.append("DCR C")
    g_code.append("JNZ %s  ; more SHL" % label1)
    g_pc += 4
    if not left:
        g_code.append("MOV C,E  ; SHL right")
        g_pc += 1
        if leftWidth == 2:
            g_code.append("MOV D,B")
            g_pc += 1
    return leftWidth
    
    
def builtin_ror(node, left):
    """Generate code for builtin ROR() procedure"""
    global g_pc, g_code
    #print("ROR:", left)
    (leftWidth, rightWidth) = node.get_args()
    if (leftWidth != 1) or (rightWidth != 1):
        fatal("SHL arg overflow")
    label1 = new_label()
    emit_label(label1)
    g_code.append("MOV A,E")
    g_code.append("RRC  ; ROR")
    g_code.append("MOV E,A")
    g_code.append("DCR C")
    g_code.append("JNZ %s  ; more ROR" % label1)
    g_pc += 7
    if not left:
        g_code.append("MOV C,E  ; ROR right")
        g_pc += 1
    return 1
    
    
def builtin_rol(node, left):
    """Generate code for builtin ROL() procedure"""
    global g_pc, g_code
    #print("ROL:", left)
    (leftWidth, rightWidth) = node.get_args()
    if (leftWidth != 1) or (rightWidth != 1):
        warning("ROL arg overflow")
    label1 = new_label()
    emit_label(label1)
    g_code.append("MOV A,E")
    g_code.append("RLC  ; ROL")
    g_code.append("MOV E,A")
    g_code.append("DCR C")
    g_code.append("JNZ %s  ; more ROL" % label1)
    g_pc += 7
    if not left:
        g_code.append("MOV C,E  ; ROL right")
        g_pc += 1
    return 1
    
    
def pop2(idx, removeSize):
    """Remove two instructions"""
    global g_pc, g_code
    g_code.pop(idx + 1)
    g_code.pop(idx)
    g_pc -= removeSize
    
    
def replace2(idx, newLine, removeSize):
    """Replace two instructions with one"""
    global g_pc, g_code
    g_code.pop(idx + 1)
    g_code.pop(idx)
    g_code.insert(idx, newLine)
    g_pc -= removeSize
    
    
def opt0():
    global g_code
    for n in range(len(g_code) - 1):
        thisn = strip_comment(g_code[n])
        nextn = strip_comment(g_code[n+1])
        if (thisn == 'XCHG') and (nextn == 'XCHG'):
            print("opt: XCHG")
            pop2(n, 2)
            return True
        elif (thisn == 'MOV C,M') and (nextn == 'MOV A,C'):
            print("opt: MOVMCA")
            replace2(n, "MOV A,M  ; OPT MOVMCA", 1)
            return True
    return False
    
    
def opt1():
    global g_code
    for n in range(len(g_code) - 1):
        thisn = strip_arg2(g_code[n])
        nextn = strip_arg2(g_code[n+1])
        if (thisn == "MVI E") and (nextn == "MVI D"):
            print("opt: MVIED")
            low = int(get_arg2(g_code[n]).rstrip('H'), 16)
            high = int(get_arg2(g_code[n+1]).rstrip('H'), 16)
            replace2(n, "LXI D,%05XH  ; OPT MVIED" % ((high << 8) + low), 1)
            return True
        elif (thisn == "MVI C") and (nextn == "MVI B"):
            print("opt: MVICB")
            low = int(get_arg2(g_code[n]).rstrip('H'), 16)
            high = int(get_arg2(g_code[n+1]).rstrip('H'), 16)
            replace2(n, "LXI B,%05XH  ; OPT MVICB" % ((high << 8) + low), 1)
            return True
        elif (thisn == "MVI C") and (nextn == "MOV A"):
            reg = get_arg2(g_code[n+1])
            if reg == 'C':
                print("opt: MVICA")
                val = int(get_arg2(g_code[n]).rstrip('H'), 16)
                replace2(n, "MVI A,%03XH  ; OPT MVICA" % val, 1)
                return True
    return False
    
    
def opt2():
    global g_code
    for n in range(len(g_code) - 1):
        thisn = get_instr(g_code[n])
        nextn = get_instr(g_code[n+1])
        if (thisn == "CALL")  and (nextn == "RET"):
                print("opt: CALLRET")
                addr = get_arg1(g_code[n])
                replace2(n, "JMP %s  ; OPT CALLRET" % addr, 1)
                return True
    return False
        
        
def optimize():
    """Perform optimization on a code block"""
    opt = True
    while opt:
        opt = opt0()
    opt = True
    while opt:
        opt = opt1()
    opt = True
    while opt:
        opt = opt2()
        
           
def output_code(cdata):
    """Write a code block to the output file"""
    global g_fout
    for line in cdata:
        g_fout.write("\t%s\n" % line)
        

def output_array(sym):
    """Write an array data symbol to the output file"""
    global g_fout, g_data_init
    
    # skip arrays referencing addresses
    if isinstance(sym, (BasedArray, AtArray)):
        return
        
    # optionally initialize uninit variables
    if g_data_init and (sym.value is None):
        sym.value = [0] * (sym.size // sym.elem_size)
        
    if sym.elem_size == 1:
        # just allocate storage
        outstr = "%s\tDB  " % sym.name
        if sym.value is None:
            outstr += "%d  DUP(?)" % sym.size
        # create a list of initial values
        else:
            for n in range(len(sym.value)):
                outstr += "%03XH" % sym.value[n]
                if n != (len(sym.value) - 1):
                    outstr += ","
    else:
        # just allocate storage
        outstr = "%s\tDW  " % sym.name 
        if sym.value is None:
            outstr += "%d  DUP(?)" % (sym.size >> 1)
        # create a list of initial values
        else:
            for n in range(len(sym.value)):
                outstr += "%05XH" % sym.value[n]
                if n != (len(sym.value) - 1):
                    outstr += ","
                    
    outstr += "    ; %04x\n" % sym.addr
    g_fout.write(outstr)
    
    
def output_variable(sym):
    """Write a data variable symbol to the output file"""
    global g_fout
    
    # skip variables referenced by address
    if isinstance(sym, (BasedVariable, BasedStruct, AtVariable)):
        return
        
    # optionally initialize uninit data variables
    if g_data_init and (sym.value is None):
        sym.value = 0
    
    # no data, just allocate storage
    if sym.value is None:
        if sym.size == 1:
            outstr = "%s\tDS  1" % sym.name
        else:
            outstr = "%s\tDS  2" % sym.name
            
    # create initialized variable
    else:
        if sym.size == 1:
            outstr = "%s\tDB  %03XH" % (sym.name, sym.value)
        else:
            outstr = "%s\tDW  " % sym.name  
            if isinstance(sym.value, Reference):
                outstr += sym.value.name
            else:
                outstr += "%05XH" % sym.value
                
    outstr += "    ; %04x\n" % sym.addr
    g_fout.write(outstr)
    
    
def output_header():
    """Create the output file header"""
    global g_fout
    g_fout.write(";\n")
    g_fout.write("; File generated by pyplm compiler\n")
    g_fout.write(";\n")
    g_fout.write("\n\tORG 0100H\n\n")
    
    
def output_trailer_hlt():
    global g_fout
    g_fout.write("\tHLT  ; halt\n")
    return 1
    
    
def output_trailer_mon():
    global g_fout
    g_fout.write("\tRST 001H  ; go to MON80 debug trap\n")
    return 1
    
    
def output_trailer_ret():
    global g_fout
    g_fout.write("\tRET  ; return to caller (CP/M ...)\n")
    return 1
    
def output_trailer(trailer):
    """Create the output file trailer.  This is the code which
       runs at program exit."""
    global g_fout, g_pc
    g_fout.write("__ENDCOM:\n")
    if trailer == "mon":
        size = output_trailer_mon()
    elif trailer == "hlt":
        size = output_trailer_hlt()
    else:
        size = output_trailer_ret()
 
 
def output_external(externName):
    """Merge an external assembly file into the output file"""
    global g_fout
    extFile = open(externName, "rt")
    g_fout.write("\n")
    for line in extFile:
        if len(line) > 1:
            g_fout.write(line)
    g_fout.write("\n")
    extFile.close()


def output(outName, externName, trailer):
    """Create the assembly output file"""
    global g_sym_list, g_fout, g_pseudo_count, g_anon_list, g_pc, g_case_list
    
    # create file and write header
    g_fout = open(outName, "wt")
    output_header()
    
    # write initialized data variables and code blocks 
    for sym in g_sym_list[g_pseudo_count:]:
        if isinstance(sym, Label):
            g_fout.write("%s:     ; %04x\n" % (sym.name, sym.addr))
        elif isinstance(sym, Array):
            output_array(sym)
        elif isinstance(sym, Variable):
            output_variable(sym)
        elif isinstance(sym, CodeBlock):
            output_code(sym.cdata)
            
    # write case tables
    for case in g_case_list:
        g_fout.write("%s:\tDW  " % case[0])
        case = case[2][1:]
        for n in range(len(case)):
            l = case[n]
            g_fout.write("%s" % l)
            if n != (len(case) - 1):
                g_fout.write(", ")
        g_fout.write("\n")
         
    # write anonymous data variables
    for sym in g_anon_list:
        if isinstance(sym, Array):
            sym.addr = g_pc
            g_pc += sym.size
            output_array(sym)
      
    # merge external procedures
    if externName is not None:
        output_external(externName)
          
    # write exit handler
    output_trailer(trailer)
    
    # write uninitialized data variables
    for sym in g_uni_list:
        if isinstance(sym, Array):
            output_array(sym)
        elif isinstance(sym, Variable):
            output_variable(sym)
        
    # mark the remainder of user memory and close file
    g_fout.write("MEMORY:\n")
    g_fout.close()
             
             
def fixup():
    global g_code, g_pc
    
    if g_entry is None:
        g_code.append("JMP __ENDCOM  ; program end")
        g_pc += 3
    else:
        g_code.append("RET  ; program end")
        g_pc += 1
    emit_code()
    #fixup_vars()
    #fixup_refs()
           
           
def init_builtins():
    global g_proc_list
    g_proc_list.append(BuiltinProcedure("LENGTH", 1, builtin_length))
    g_proc_list.append(BuiltinProcedure("LAST", 1, builtin_last))
    g_proc_list.append(BuiltinProcedure("LOW", 1, builtin_low))  
    g_proc_list.append(BuiltinProcedure("HIGH", 1, builtin_high))
    g_proc_list.append(BuiltinProcedure("DOUBLE", 1, builtin_double))
    g_proc_list.append(BuiltinProcedure("SHR", 2, builtin_shr))
    g_proc_list.append(BuiltinProcedure("SHL", 2, builtin_shl))
    g_proc_list.append(BuiltinProcedure("ROR", 2, builtin_ror))
    g_proc_list.append(BuiltinProcedure("ROL", 2, builtin_rol))
    
    
def init_pseudos():
    global g_sym_list, g_pseudo_count
    g_sym_list.append(Variable("STACKPTR", 0, 2, None))
    g_sym_list.append(Variable("ZERO", 0, 1, None))
    g_sym_list.append(Variable("CARRY", 0, 1, None))
    g_sym_list.append(Variable("SIGN", 0, 1, None))
    g_sym_list.append(Variable("PARITY", 0, 1, None))
    g_sym_list.append(Array("MEMORY", 0, 0, None, 1))
    g_pseudo_count = len(g_sym_list)


if __name__ == '__main__':

    from argparse import ArgumentParser

    argparser = ArgumentParser()
    argparser.add_argument("infile", type=str, 
                            help="input PL/M file")
    argparser.add_argument("outfile", type=str, 
                            help="output 8080 ASM file")
    argparser.add_argument("-s", "--start", action="store", type=str,
                           help="program start procedure")
    argparser.add_argument("-o", "--optimize", action="store_true",
                            help="optimize")
    argparser.add_argument("-e", "--external", action="store", type=str,
                            help="8080 ASM file containing EXTERNAL procedures")
    argparser.add_argument("-i", "--initialize", action="store_true",
                            help="initialize data variables to zero")
    argparser.add_argument("-t", "--trailer", action="store", type=str,
                           choices = ("hlt", "ret", "mon"), default="ret",
                           help="program termination option")
    args = argparser.parse_args()
    
    print(args.external)
    
    g_opt = args.optimize
    g_data_init = args.initialize
    g_entry = args.start
    
    inFile = open(args.infile, "rt")
    text = inFile.read()
    inFile.close()
    
    init_builtins()
    init_pseudos()
    
    plmlexer.input(text)
    parser.parse(text, lexer = plmlexer)
    
    if len(g_do_stack) > 0:
        fatal("missing closing END statement")
        
    fixup()
   
    #for sym in g_sym_list:
    #    print(sym)

    output(args.outfile, args.external, args.trailer)

    exit(0)
    


