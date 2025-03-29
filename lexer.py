
from copy import copy

import ply.lex as lex

states = (('comment', 'exclusive'),
          ('literal', 'exclusive'))

tokens = ['LCOMMENT',
          'ASTERIX',
          'DECLARE',
          'STRUCTURE',
          'BYTE',
          'ADDRESS',
          'BASED',
          'THEN',
          'IF',
          'ELSE',
          'WHILE',
          'END',
          'DO',
          'GO',
          'TO',
          'BY',
          'CASE',
          'LITERALLY',
          'AT',
          'DATA',
          'PROCEDURE',
          'EXTERNAL',
          'CALL',
          'RETURN',
          'ASSIGN',
          'EQUAL',
          'COLON',
          'SEMICOLON',
          'COMMA',
          'LPARENS',
          'RPARENS',
          'SQUOTE',
          'PLUS',
          'MINUS',
          'DIV',
          'MOD',
          'AND',
          'OR',
          'NOT',
          'NOTEQUAL',
          'LESSTHANEQUAL',
          'GREATERTHANEQUAL',
          'LESSTHAN',
          'GREATERTHAN',
          'PERIOD',
          'HEXNUMBER',
          'DECNUMBER',
          'BINNUMBER',
          'IDENT',
          'STRING']
          
keywords = set(  ('DECLARE',
                  'STRUCTURE',
                  'BYTE',
                  'ADDRESS',
                  'BASED',
                  'THEN',
                  'IF',
                  'ELSE',
                  'GO',
                  'TO',
                  'BY',
                  'CASE',
                  'WHILE',
                  'END',
                  'DO',
                  'LITERALLY',
                  'AT',
                  'DATA',
                  'PROCEDURE',
                  'CALL',
                  'RETURN',
                  'PROCEDURE',
                  'EXTERNAL',
                  'PLUS',
                  'MINUS',
                  'MOD',
                  'AND',
                  'OR',
                  'NOT',))
    

def t_LCOMMENT(t):
    r'\/\*'
    t.lexer.begin('comment')
    
def t_comment_RCOMMENT(t):
    r'\*\/'
    t.lexer.begin('INITIAL')
    
def t_comment_asterisk(t):
    r'\*+[^\/]'
    
def t_comment_slash(t):
    r'[^*]+\/'
    
def t_comment_string(t):
    r'[^\*\/]'
    
def t_comment_error(t):
    pass
    
def t_comment_newline(t):
    r'\n+'
    t.lexer.lineno += len(t.value)
    
t_comment_ignore = ''

def t_ASTERIX(t):
    r'\*'
    return t
    
def t_COMMA(t):
    r','
    return t
    
def t_LPARENS(t):
    r'\('
    return t
    
def t_RPARENS(t):
    r'\)'
    return t

def t_SEMICOLON(t):
    r';'
    return t
    
def t_SQUOTE(t):
    r'\''
    t.lexer.begin('literal')
    t.lexer.sbuf = ""
    return None
    
def t_literal_SQUOTE(t):
    r'\''
    if len(t.lexer.sbuf) == 1:
        t.type = 'DECNUMBER'
        t.value = ord(t.lexer.sbuf[0])
    else:
        t.type = 'STRING'
        t.value = copy(t.lexer.sbuf)
    t.lexer.begin('INITIAL')
    return t
    
def t_literal_STRING(t):
    r'[^\']+'
    t.lexer.sbuf += t.value
    return None
    
def t_literal_error(t):
    pass
    
t_literal_ignore = ''

def t_AT(t):
    r'AT'
    return t
    
def t_DATA(t):
    r'DATA'
    return t
    
def t_ASSIGN(t):
    r':='
    return t
    
def t_COLON(t):
    r':'
    return t
    
def t_NOTEQUAL(t):
    r'<>'
    return t
    
def t_LESSTHANEQUAL(t):
    r'<='
    return t
    
def t_GREATERTHANEQUAL(t):
    r'>='
    return t
    
def t_EQUAL(t):
    r'='
    return t
    
def t_LESSTHAN(t):
    r'<'
    return t
    
def t_GREATERTHAN(t):
    r'>'
    return t

def t_PLUS(t):
    r'\+'
    return t
    
def t_MINUS(t):
    r'\-'
    return t
    
def t_DIV(t):
    r'\/'
    return t
    
def t_PERIOD(t):
    r'\.'
    return t

def t_IDENT(t):
    r'[A-Za-z_][A-Za-z$\d]*'
    global keywords
    if t.value.upper() in keywords:
        t.type = t.value = t.value.upper()
    else:
        t.value = t.value.replace('$', '').upper()
    return t
    
def t_HEXNUMBER(t):
    r'[\dA-Fa-f$]+[H|h]'
    t.value = int(t.value[:-1].replace('$', ''), 16)
    return t
    
def t_BINNUMBER(t):
    r'[01$]+[B|b]'
    t.value = int(t.value[:-1].replace('$', ''), 2)
    return t

def t_DECNUMBER(t):
    #r'-?\d+'
    r'[\d$]+'
    t.value = int(t.value.replace('$', ''))
    return t
    
def t_newline(t):
    r'\n+'
    t.lexer.lineno += len(t.value)
    
t_ignore = ' \t\r'

def t_error(t):
    print("ERROR: ", t.value)

plmlexer = lex.lex()


if __name__ == '__main__':

    stFile = open("ptest.plm", "rt")
    stText = stFile.read()
    stFile.close()
    
    plmlexer.literal_dict = {'MYVAL' : '12h'}
    plmlexer.input(stText)

    t = plmlexer.token()
    while t:
        print(t)
        t = plmlexer.token()



