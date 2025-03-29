

class Symbol(object):

    def __init__(self, name, addr, size):
        self.name = name
        self.size = size
        self.addr = addr
        
    def __repr__(self):
        return "Symbol(%s,0x%04x, %d)" % (self.name, self.addr, self.size)
        
class Variable(Symbol):

    def __init__(self, name, addr, size, value):
        Symbol.__init__(self, name, addr, size)
        self.value = value
        
    def __repr__(self):
        return "Variable(%s,0x%04x,%s,%s)" % (self.name, self.addr, self.size, self.value) 

class Reference(Variable):

    def __init__(self, name):
        Variable.__init__(self, name, 0, 2, None)
        
    def __repr__(self):
        return "Reference(.%s)" % self.name

class Array(Variable):

    def __init__(self, name, addr, size, value, elemSize):
        Variable.__init__(self, name, addr, size, value)
        self.elem_size = elemSize
        
    def __repr__(self):
        return "Array(%s,%s,%s,%s,%s)" % (self.name, self.addr, self.size, self.value, self.elem_size)

class AtArray(Array):

    def __repr__(self):
        return "AtArray(%s,%s,%s,%s)" % (self.name, self.addr, self.size, self.elem_size)
    
class BasedArray(Array):
    
    def __repr__(self):
        return "BasedArray(%s,%s,%s,%s)" % (self.name, self.addr, self.size, self.elem_size)

class AtVariable(Variable):

    def __repr__(self):
        return "AtVariable(%s,%s,%s)" % (self.name, self.addr, self.size)

class BasedVariable(Variable):

    def __repr__(self):
        return "BasedVariable(%s,%s,%s,%s)" % (self.name, self.addr, self.size, self.value) 

class Struct(Variable): pass

class BasedStruct(Struct):

    def __repr__(self):
        return "BasedStruct(%s,%s,%s,%s)" % (self.name, self.addr, self.size, self.value)

class Label(Symbol):

    def __init__(self, name, addr):
        Symbol.__init__(self, name, addr, 0)

    def __repr__(self):
        return "Label(%s,0x%04x)" % (self.name, self.addr)
        
class CodeBlock(Symbol):

    def __init__(self, addr, size, cdata):
        Symbol.__init__(self, '', addr, size)
        self.cdata = cdata
        
    def __repr__(self):
        return "CodeBlock(0x%04x,%s,%s)" % (self.addr, self.size, self.cdata) 
        
class Procedure(Symbol):
    
    def __init__(self, name, numArgs, retSize):
        Symbol.__init__(self, name, 0, retSize)
        self.num_args = numArgs
        
    def __repr__(self):
        return "Procedure(%s,%d,%d)" % (self.name, self.num_args, self.size)
       
class BuiltinProcedure(Procedure):

    def __init__(self, name, numArgs, handler):
        Procedure.__init__(self, name, numArgs, -1)
        self.handler = handler
        
class UserProcedure(Procedure):

    def __init__(self, name, numArgs, retSize, argNames = ()):
        Procedure.__init__(self, name, numArgs, retSize)
        self.arg_names = argNames
        self.arg_widths = [None] * numArgs
        
class ExternalProcedure(UserProcedure): pass

def strip_comment(line):
    """Remove any comment from a line of code."""
    p = line.find(';')
    if p > 0:
        return line[:p].rstrip()
    else:
        return line.rstrip()
        
def strip_arg2(line):
    """Remove the second instruction argument from a line of code."""
    s = strip_comment(line)
    p = s.rfind(',')
    if p > 0:
        return s[:p].rstrip()
    else:
        return s.rstrip()
        
def get_arg2(line):
    """Get the second instruction argument from a line of code.
       Return None if no second argument."""
    s = strip_comment(line)
    p = s.rfind(',')
    if p > 0:
        return s[p+1:].strip()
    else:
        return None
    
def get_arg1(line):
    """Get the first instruction argument from a line of code.
       Return None if no first argument"""
    s = strip_comment(line)
    p = s.rfind(',')
    if p > 0:
        s = s[:p]
    sl = s.split()
    if len(sl) > 1:
        return sl[1].strip()
    else:
        return None
        
def get_instr(line):
    """Get just the instruction from a line of code"""
    sl = line.split()
    return sl[0].strip()
        
def fatal(msg):
    """Print error message and exit with failure code"""
    print("ERROR:", msg)
    exit(-1)

def warning(msg):
    """Print warning message"""
    print("WARNING:", msg)