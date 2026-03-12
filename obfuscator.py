"""
Main obfuscation pipeline - ties together all passes
"""
from lexer import Lexer, LexerError
from parser import Parser, ParseError
from vm import Compiler, generate_vm_lua

class ObfuscationError(Exception):
    pass

def obfuscate(source: str, options: dict = None) -> str:
    """
    Full obfuscation pipeline:
    1. Lex source
    2. Parse to AST
    3. Compile to custom bytecode
    4. Generate VM + bytecode as Lua
    5. Apply post-processing passes
    """
    if options is None:
        options = {}

    try:
        lexer = Lexer(source)
        tokens = lexer.tokenize()
    except LexerError as e:
        raise ObfuscationError(f"Lexer error: {e}")

    try:
        parser = Parser(tokens)
        ast = parser.parse()
    except ParseError as e:
        raise ObfuscationError(f"Parse error: {e}")

    try:
        compiler = Compiler()
        proto = compiler.compile(ast)
    except Exception as e:
        raise ObfuscationError(f"Compiler error: {e}")

    try:
        result = generate_vm_lua(proto)
    except Exception as e:
        raise ObfuscationError(f"VM generation error: {e}")

    return result
