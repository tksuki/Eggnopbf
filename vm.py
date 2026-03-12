"""
Custom VM - Luraph-style bytecode compiler and Lua VM runtime generator.
Compiles Lua AST to custom bytecode, then wraps it in a Lua VM interpreter.
"""
import random
import string
from parser import *  # 修正: from .parser import * -> from parser import *

# Opcodes
class Op:
    LOADK    = 0
    LOADNIL  = 1
    LOADBOOL = 2
    MOVE     = 3
    GETGLOBAL= 4
    SETGLOBAL= 5
    GETTABLE = 6
    SETTABLE = 7
    NEWTABLE = 8
    ADD      = 9
    SUB      = 10
    MUL      = 11
    DIV      = 12
    MOD      = 13
    POW      = 14
    UNM      = 15
    NOT      = 16
    LEN      = 17
    CONCAT   = 18
    JMP      = 19
    EQ       = 20
    LT       = 21
    LE       = 22
    TEST     = 23
    TESTSET  = 24
    CALL     = 25
    TAILCALL = 26
    RETURN   = 27
    FORLOOP  = 28
    FORPREP  = 29
    TFORLOOP = 30
    SETLIST  = 31
    CLOSE    = 32
    CLOSURE  = 33
    VARARG   = 34
    SELF     = 35
    IDIV     = 36
    BAND     = 37
    BOR      = 38
    BXOR     = 39
    SHL      = 40
    SHR      = 41
    BNOT     = 42
    GETUPVAL = 43
    SETUPVAL = 44
    GETTABUP = 45
    SETTABUP = 46

class Instruction:
    def __init__(self, op, a=0, b=0, c=0, bx=0, sbx=0):
        self.op = op
        self.a = a
        self.b = b
        self.c = c
        self.bx = bx
        self.sbx = sbx

class Proto:
    def __init__(self):
        self.instructions = []
        self.constants = []
        self.protos = []
        self.upvalues = []
        self.params = 0
        self.is_vararg = False
        self.max_stack = 10

    def add_const(self, val):
        try:
            return self.constants.index(val)
        except ValueError:
            self.constants.append(val)
            return len(self.constants) - 1

    def emit(self, op, a=0, b=0, c=0, bx=0, sbx=0):
        self.instructions.append(Instruction(op, a, b, c, bx, sbx))
        return len(self.instructions) - 1

    def patch_jump(self, idx, target):
        self.instructions[idx].sbx = target - idx - 1


class Compiler:
    def __init__(self):
        self.proto = None
        self.reg = 0
        self.locals = {}
        self.local_stack = []

    def compile(self, ast):
        self.proto = Proto()
        self.proto.is_vararg = True
        self.reg = 0
        self.locals = {}
        self.local_stack = []
        self.compile_block(ast)
        self.proto.emit(Op.RETURN, 0, 1)
        return self.proto

    def alloc_reg(self):
        r = self.reg
        self.reg += 1
        if self.reg > self.proto.max_stack:
            self.proto.max_stack = self.reg
        return r

    def free_reg(self):
        self.reg -= 1

    def push_scope(self):
        self.local_stack.append(dict(self.locals))

    def pop_scope(self):
        if self.local_stack:
            self.locals = self.local_stack.pop()

    def define_local(self, name):
        r = self.alloc_reg()
        self.locals[name] = r
        return r

    def resolve_local(self, name):
        return self.locals.get(name, None)

    def compile_block(self, block):
        self.push_scope()
        for stmt in block.stmts:
            self.compile_stmt(stmt)
        if block.ret:
            self.compile_return(block.ret)
        self.pop_scope()

    def compile_stmt(self, stmt):
        if isinstance(stmt, AssignStmt):
            self.compile_assign(stmt)
        elif isinstance(stmt, LocalStmt):
            self.compile_local(stmt)
        elif isinstance(stmt, CallStmt):
            self.compile_call_stmt(stmt)
        elif isinstance(stmt, DoStmt):
            self.compile_block(stmt.block)
        elif isinstance(stmt, WhileStmt):
            self.compile_while(stmt)
        elif isinstance(stmt, RepeatStmt):
            self.compile_repeat(stmt)
        elif isinstance(stmt, IfStmt):
            self.compile_if(stmt)
        elif isinstance(stmt, ForNumStmt):
            self.compile_fornum(stmt)
        elif isinstance(stmt, ForInStmt):
            self.compile_forin(stmt)
        elif isinstance(stmt, FuncStmt):
            self.compile_func_stmt(stmt)
        elif isinstance(stmt, LocalFuncStmt):
            self.compile_local_func(stmt)
        elif isinstance(stmt, ReturnStmt):
            self.compile_return(stmt)
        elif isinstance(stmt, BreakStmt):
            pass  # handled by loop
        elif isinstance(stmt, GotoStmt):
            pass
        elif isinstance(stmt, LabelStmt):
            pass

    def compile_return(self, stmt):
        if not stmt.values:
            self.proto.emit(Op.RETURN, 0, 1)
            return
        base = self.reg
        for val in stmt.values:
            r = self.alloc_reg()
            self.compile_expr_to(val, r)
        self.proto.emit(Op.RETURN, base, len(stmt.values) + 1)
        for _ in stmt.values:
            self.free_reg()

    def compile_assign(self, stmt):
        regs = []
        for val in stmt.values:
            r = self.alloc_reg()
            self.compile_expr_to(val, r)
            regs.append(r)
        for i, target in enumerate(stmt.targets):
            src = regs[i] if i < len(regs) else None
            if src is None:
                src = self.alloc_reg()
                self.proto.emit(Op.LOADNIL, src, src)
                regs.append(src)
            self.compile_assign_target(target, src)
        for r in reversed(regs):
            self.free_reg()

    def compile_assign_target(self, target, src):
        if isinstance(target, NameExpr):
            loc = self.resolve_local(target.name)
            if loc is not None:
                self.proto.emit(Op.MOVE, loc, src)
            else:
                k = self.proto.add_const(target.name)
                self.proto.emit(Op.SETGLOBAL, src, bx=k)
        elif isinstance(target, FieldExpr):
            t = self.alloc_reg()
            self.compile_expr_to(target.table, t)
            k = self.proto.add_const(target.field)
            self.proto.emit(Op.SETTABLE, t, 256 + k, src)
            self.free_reg()
        elif isinstance(target, IndexExpr):
            t = self.alloc_reg()
            self.compile_expr_to(target.table, t)
            ki = self.alloc_reg()
            self.compile_expr_to(target.key, ki)
            self.proto.emit(Op.SETTABLE, t, ki, src)
            self.free_reg()
            self.free_reg()

    def compile_local(self, stmt):
        regs = []
        for i, name in enumerate(stmt.names):
            r = self.alloc_reg()
            if i < len(stmt.values):
                self.compile_expr_to(stmt.values[i], r)
            else:
                self.proto.emit(Op.LOADNIL, r, r)
            regs.append(r)
        for i, name in enumerate(stmt.names):
            self.locals[name] = regs[i]

    def compile_call_stmt(self, stmt):
        r = self.alloc_reg()
        self.compile_expr_to(stmt.expr, r)
        self.free_reg()

    def compile_while(self, stmt):
        start = len(self.proto.instructions)
        cond_reg = self.alloc_reg()
        self.compile_expr_to(stmt.cond, cond_reg)
        jmp = self.proto.emit(Op.TEST, cond_reg, 0, 0)
        jmp2 = self.proto.emit(Op.JMP, 0, sbx=0)
        self.free_reg()
        self.compile_block(stmt.block)
        back = self.proto.emit(Op.JMP, 0, sbx=start - len(self.proto.instructions) - 1)
        self.proto.patch_jump(jmp2, len(self.proto.instructions))

    def compile_repeat(self, stmt):
        start = len(self.proto.instructions)
        self.compile_block(stmt.block)
        cond_reg = self.alloc_reg()
        self.compile_expr_to(stmt.cond, cond_reg)
        self.proto.emit(Op.TEST, cond_reg, 0, 0)
        self.proto.emit(Op.JMP, 0, sbx=start - len(self.proto.instructions) - 1)
        self.free_reg()

    def compile_if(self, stmt):
        exits = []
        cond_reg = self.alloc_reg()
        self.compile_expr_to(stmt.cond, cond_reg)
        jmp_false = self.proto.emit(Op.TEST, cond_reg, 0, 0)
        jmp_skip = self.proto.emit(Op.JMP, 0, sbx=0)
        self.free_reg()
        self.compile_block(stmt.then_block)
        exits.append(self.proto.emit(Op.JMP, 0, sbx=0))
        self.proto.patch_jump(jmp_skip, len(self.proto.instructions))
        for (ec, eb) in stmt.elseifs:
            cr = self.alloc_reg()
            self.compile_expr_to(ec, cr)
            jf = self.proto.emit(Op.TEST, cr, 0, 0)
            js = self.proto.emit(Op.JMP, 0, sbx=0)
            self.free_reg()
            self.compile_block(eb)
            exits.append(self.proto.emit(Op.JMP, 0, sbx=0))
            self.proto.patch_jump(js, len(self.proto.instructions))
        if stmt.else_block:
            self.compile_block(stmt.else_block)
        for e in exits:
            self.proto.patch_jump(e, len(self.proto.instructions))

    def compile_fornum(self, stmt):
        base = self.reg
        r_init = self.alloc_reg()
        r_limit = self.alloc_reg()
        r_step = self.alloc_reg()
        r_var = self.alloc_reg()
        self.compile_expr_to(stmt.start, r_init)
        self.compile_expr_to(stmt.stop, r_limit)
        if stmt.step:
            self.compile_expr_to(stmt.step, r_step)
        else:
            k = self.proto.add_const(1)
            self.proto.emit(Op.LOADK, r_step, bx=k)
        prep = self.proto.emit(Op.FORPREP, base, sbx=0)
        self.locals[stmt.name] = r_var
        self.compile_block(stmt.block)
        loop = self.proto.emit(Op.FORLOOP, base, sbx=0)
        self.proto.patch_jump(prep, loop)
        self.proto.patch_jump(loop, prep + 1)
        self.reg = base

    def compile_forin(self, stmt):
        base = self.reg
        r_iter = self.alloc_reg()
        r_state = self.alloc_reg()
        r_ctrl = self.alloc_reg()
        if stmt.iters:
            self.compile_expr_to(stmt.iters[0], r_iter)
        if len(stmt.iters) > 1:
            self.compile_expr_to(stmt.iters[1], r_state)
        if len(stmt.iters) > 2:
            self.compile_expr_to(stmt.iters[2], r_ctrl)
        jmp = self.proto.emit(Op.JMP, 0, sbx=0)
        loop_start = len(self.proto.instructions)
        var_regs = []
        for name in stmt.names:
            r = self.alloc_reg()
            self.locals[name] = r
            var_regs.append(r)
        self.compile_block(stmt.block)
        self.proto.patch_jump(jmp, len(self.proto.instructions))
        self.proto.emit(Op.TFORLOOP, base, c=len(stmt.names))
        self.proto.emit(Op.JMP, 0, sbx=loop_start - len(self.proto.instructions) - 1)
        self.reg = base

    def compile_func_stmt(self, stmt):
        sub = self.compile_func(stmt.params, stmt.has_vararg, stmt.block)
        idx = len(self.proto.protos)
        self.proto.protos.append(sub)
        r = self.alloc_reg()
        self.proto.emit(Op.CLOSURE, r, bx=idx)
        name = '.'.join(stmt.name)
        if stmt.method:
            name += ':' + stmt.method
        k = self.proto.add_const(name)
        self.proto.emit(Op.SETGLOBAL, r, bx=k)
        self.free_reg()

    def compile_local_func(self, stmt):
        r = self.define_local(stmt.name)
        sub = self.compile_func(stmt.params, stmt.has_vararg, stmt.block)
        idx = len(self.proto.protos)
        self.proto.protos.append(sub)
        self.proto.emit(Op.CLOSURE, r, bx=idx)

    def compile_func(self, params, has_vararg, block):
        old_proto = self.proto
        old_reg = self.reg
        old_locals = self.locals
        old_stack = self.local_stack
        self.proto = Proto()
        self.proto.params = len(params)
        self.proto.is_vararg = has_vararg
        self.reg = 0
        self.locals = {}
        self.local_stack = []
        for p in params:
            self.locals[p] = self.alloc_reg()
        self.compile_block(block)
        self.proto.emit(Op.RETURN, 0, 1)
        result = self.proto
        self.proto = old_proto
        self.reg = old_reg
        self.locals = old_locals
        self.local_stack = old_stack
        return result

    def compile_expr_to(self, expr, reg):
        if isinstance(expr, NumberExpr):
            k = self.proto.add_const(float(expr.value.replace('_', '')))
            self.proto.emit(Op.LOADK, reg, bx=k)
        elif isinstance(expr, StringExpr):
            k = self.proto.add_const(expr.value)
            self.proto.emit(Op.LOADK, reg, bx=k)
        elif isinstance(expr, BoolExpr):
            self.proto.emit(Op.LOADBOOL, reg, 1 if expr.value else 0)
        elif isinstance(expr, NilExpr):
            self.proto.emit(Op.LOADNIL, reg, reg)
        elif isinstance(expr, VarArgExpr):
            self.proto.emit(Op.VARARG, reg, 0)
        elif isinstance(expr, NameExpr):
            loc = self.resolve_local(expr.name)
            if loc is not None:
                self.proto.emit(Op.MOVE, reg, loc)
            else:
                k = self.proto.add_const(expr.name)
                self.proto.emit(Op.GETGLOBAL, reg, bx=k)
        elif isinstance(expr, FieldExpr):
            t = self.alloc_reg()
            self.compile_expr_to(expr.table, t)
            k = self.proto.add_const(expr.field)
            self.proto.emit(Op.GETTABLE, reg, t, 256 + k)
            self.free_reg()
        elif isinstance(expr, IndexExpr):
            t = self.alloc_reg()
            self.compile_expr_to(expr.table, t)
            ki = self.alloc_reg()
            self.compile_expr_to(expr.key, ki)
            self.proto.emit(Op.GETTABLE, reg, t, ki)
            self.free_reg()
            self.free_reg()
        elif isinstance(expr, BinOpExpr):
            self.compile_binop(expr, reg)
        elif isinstance(expr, UnOpExpr):
            self.compile_unop(expr, reg)
        elif isinstance(expr, CallExpr):
            self.compile_call(expr, reg)
        elif isinstance(expr, MethodCallExpr):
            self.compile_method_call(expr, reg)
        elif isinstance(expr, FuncExpr):
            sub = self.compile_func(expr.params, expr.has_vararg, expr.block)
            idx = len(self.proto.protos)
            self.proto.protos.append(sub)
            self.proto.emit(Op.CLOSURE, reg, bx=idx)
        elif isinstance(expr, TableExpr):
            self.compile_table(expr, reg)

    def compile_binop(self, expr, reg):
        op_map = {
            '+': Op.ADD, '-': Op.SUB, '*': Op.MUL, '/': Op.DIV,
            '%': Op.MOD, '^': Op.POW, '//': Op.IDIV,
            '&': Op.BAND, '|': Op.BOR, '~': Op.BXOR,
            '<<': Op.SHL, '>>': Op.SHR, '..': Op.CONCAT,
        }
        cmp_map = {'==': Op.EQ, '~=': Op.EQ, '<': Op.LT, '>': Op.LT,
                   '<=': Op.LE, '>=': Op.LE}
        if expr.op in op_map:
            l = self.alloc_reg()
            r = self.alloc_reg()
            self.compile_expr_to(expr.left, l)
            self.compile_expr_to(expr.right, r)
            self.proto.emit(op_map[expr.op], reg, l, r)
            self.free_reg()
            self.free_reg()
        elif expr.op in cmp_map:
            l = self.alloc_reg()
            r = self.alloc_reg()
            self.compile_expr_to(expr.left, l)
            self.compile_expr_to(expr.right, r)
            inv = 1 if expr.op in ('~=', '>', '>=') else 0
            if expr.op in ('>', '>='):
                l, r = r, l
            self.proto.emit(cmp_map[expr.op], inv, l, r)
            self.proto.emit(Op.JMP, 0, sbx=1)
            self.proto.emit(Op.LOADBOOL, reg, 0, 1)
            self.proto.emit(Op.LOADBOOL, reg, 1, 0)
            self.free_reg()
            self.free_reg()
        elif expr.op == 'and':
            self.compile_expr_to(expr.left, reg)
            j = self.proto.emit(Op.TESTSET, reg, reg, 0)
            jmp = self.proto.emit(Op.JMP, 0, sbx=0)
            self.compile_expr_to(expr.right, reg)
            self.proto.patch_jump(jmp, len(self.proto.instructions))
        elif expr.op == 'or':
            self.compile_expr_to(expr.left, reg)
            j = self.proto.emit(Op.TESTSET, reg, reg, 1)
            jmp = self.proto.emit(Op.JMP, 0, sbx=0)
            self.compile_expr_to(expr.right, reg)
            self.proto.patch_jump(jmp, len(self.proto.instructions))

    def compile_unop(self, expr, reg):
        op_map = {'-': Op.UNM, 'not': Op.NOT, '#': Op.LEN, '~': Op.BNOT}
        r = self.alloc_reg()
        self.compile_expr_to(expr.operand, r)
        self.proto.emit(op_map.get(expr.op, Op.UNM), reg, r)
        self.free_reg()

    def compile_call(self, expr, reg):
        f = self.alloc_reg()
        self.compile_expr_to(expr.func, f)
        for arg in expr.args:
            ar = self.alloc_reg()
            self.compile_expr_to(arg, ar)
        self.proto.emit(Op.CALL, f, len(expr.args) + 1, 2)
        self.proto.emit(Op.MOVE, reg, f)
        for _ in expr.args:
            self.free_reg()
        self.free_reg()

    def compile_method_call(self, expr, reg):
        obj = self.alloc_reg()
        self.compile_expr_to(expr.obj, obj)
        k = self.proto.add_const(expr.method)
        method_reg = self.alloc_reg()
        self.proto.emit(Op.SELF, obj, obj, 256 + k)
        for arg in expr.args:
            ar = self.alloc_reg()
            self.compile_expr_to(arg, ar)
        self.proto.emit(Op.CALL, obj, len(expr.args) + 2, 2)
        self.proto.emit(Op.MOVE, reg, obj)
        for _ in expr.args:
            self.free_reg()
        self.free_reg()
        self.free_reg()

    def compile_table(self, expr, reg):
        self.proto.emit(Op.NEWTABLE, reg, 0, 0)
        for i, field in enumerate(expr.fields):
            vr = self.alloc_reg()
            self.compile_expr_to(field.value, vr)
            if field.key is None:
                k = self.proto.add_const(i + 1)
                self.proto.emit(Op.SETTABLE, reg, 256 + k, vr)
            else:
                kr = self.alloc_reg()
                self.compile_expr_to(field.key, kr)
                self.proto.emit(Op.SETTABLE, reg, kr, vr)
                self.free_reg()
            self.free_reg()


def rand_name(length=8):
    chars = string.ascii_letters + string.digits
    first = random.choice(string.ascii_letters + '_')
    rest = ''.join(random.choices(chars + '_', k=length - 1))
    return first + rest

def obfuscate_name(length=12):
    # Generate names that look like Luraph output: mix of l, I, 1
    confusing = ['l', 'I', '1', 'O', '0']
    return ''.join(random.choices(confusing, k=length))


def serialize_proto_to_lua(proto, vm_names, depth=0):
    """Serialize a Proto to a Lua table literal for the VM"""
    instr_parts = []
    for ins in proto.instructions:
        instr_parts.append(f"{{{ins.op},{ins.a},{ins.b},{ins.c},{ins.bx},{ins.sbx}}}")
    
    const_parts = []
    for c in proto.constants:
        if isinstance(c, str):
            escaped = c.replace('\\', '\\\\').replace('"', '\\"').replace('\n', '\\n').replace('\r', '\\r').replace('\0', '\\0')
            const_parts.append(f'"{escaped}"')
        elif isinstance(c, float):
            const_parts.append(repr(c))
        elif c is None:
            const_parts.append('false')
        else:
            const_parts.append(str(c))
    
    sub_parts = []
    for sub in proto.protos:
        sub_parts.append(serialize_proto_to_lua(sub, vm_names, depth + 1))
    
    return (
        f"{{{vm_names['instructions']}={{{','.join(instr_parts)}}},"
        f"{vm_names['constants']}={{{','.join(const_parts)}}},"
        f"{vm_names['protos']}={{{','.join(sub_parts)}}},"
        f"{vm_names['params']}={proto.params},"
        f"{vm_names['is_vararg']}={'true' if proto.is_vararg else 'false'},"
        f"{vm_names['max_stack']}={proto.max_stack}}}"
    )


def generate_vm_lua(proto):
    """Generate full obfuscated VM + bytecode as Lua source"""
    # Generate random names for VM internals
    vm = {n: obfuscate_name(random.randint(8, 14)) for n in [
        'execute', 'wrap', 'stack', 'pc', 'upvals', 'env',
        'instructions', 'constants', 'protos', 'params', 'is_vararg', 'max_stack',
        'ins', 'op', 'a', 'b', 'c', 'bx', 'sbx',
        'proto', 'func', 'args', 'results', 'i', 'k', 'v',
        'top', 'base', 'closure', 'self_ref'
    ]}
    
    bytecode = serialize_proto_to_lua(proto, vm)
    
    # XOR-encrypt the bytecode string with a random key
    key = random.randint(1, 255)
    
    # Build the VM runtime in Lua
    lua_vm = f"""-- [[ VM RUNTIME ]]
local {vm['execute']}
{vm['execute']} = function({vm['proto']}, {vm['env']}, ...)
  local {vm['stack']} = {{}}
  local {vm['pc']} = 1
  local {vm['upvals']} = {{}}
  local {vm['instructions']} = {vm['proto']}.{vm['instructions']}
  local {vm['constants']} = {vm['proto']}.{vm['constants']}
  local {vm['protos']} = {vm['proto']}.{vm['protos']}
  -- Load params
  local {vm['args']} = {{...}}
  for {vm['i']} = 1, {vm['proto']}.{vm['params']} do
    {vm['stack']}[{vm['i']}] = {vm['args']}[{vm['i']}]
  end
  if {vm['proto']}.{vm['is_vararg']} then
    {vm['stack']}[0] = {vm['args']}
  end
  local function {vm['k']}({vm['v']})
    if {vm['v']} >= 256 then return {vm['constants']}[{vm['v']}-255] end
    return {vm['stack']}[{vm['v']}]
  end
  while true do
    local {vm['ins']} = {vm['instructions']}[{vm['pc']}]
    local {vm['op']} = {vm['ins']}[1]
    local {vm['a']} = {vm['ins']}[2]
    local {vm['b']} = {vm['ins']}[3]
    local {vm['c']} = {vm['ins']}[4]
    local {vm['bx']} = {vm['ins']}[5]
    local {vm['sbx']} = {vm['ins']}[6]
    {vm['pc']} = {vm['pc']} + 1
    if {vm['op']} == {Op.LOADK} then
      {vm['stack']}[{vm['a']}] = {vm['constants']}[{vm['bx']}+1]
    elseif {vm['op']} == {Op.LOADNIL} then
      for {vm['i']}={vm['a']},{vm['b']} do {vm['stack']}[{vm['i']}]=nil end
    elseif {vm['op']} == {Op.LOADBOOL} then
      {vm['stack']}[{vm['a']}] = ({vm['b']}~=0)
      if {vm['c']}~=0 then {vm['pc']}={vm['pc']}+1 end
    elseif {vm['op']} == {Op.MOVE} then
      {vm['stack']}[{vm['a']}] = {vm['stack']}[{vm['b']}]
    elseif {vm['op']} == {Op.GETGLOBAL} then
      {vm['stack']}[{vm['a']}] = {vm['env']}[{vm['constants']}[{vm['bx']}+1]]
    elseif {vm['op']} == {Op.SETGLOBAL} then
      {vm['env']}[{vm['constants']}[{vm['bx']}+1]] = {vm['stack']}[{vm['a']}]
    elseif {vm['op']} == {Op.GETTABLE} then
      {vm['stack']}[{vm['a']}] = {vm['stack']}[{vm['b']}][{vm['k']}({vm['c']})]
    elseif {vm['op']} == {Op.SETTABLE} then
      {vm['stack']}[{vm['a']}][{vm['k']}({vm['b']})] = {vm['k']}({vm['c']})
    elseif {vm['op']} == {Op.NEWTABLE} then
      {vm['stack']}[{vm['a']}] = {{}}
    elseif {vm['op']} == {Op.ADD} then
      {vm['stack']}[{vm['a']}] = {vm['k']}({vm['b']}) + {vm['k']}({vm['c']})
    elseif {vm['op']} == {Op.SUB} then
      {vm['stack']}[{vm['a']}] = {vm['k']}({vm['b']}) - {vm['k']}({vm['c']})
    elseif {vm['op']} == {Op.MUL} then
      {vm['stack']}[{vm['a']}] = {vm['k']}({vm['b']}) * {vm['k']}({vm['c']})
    elseif {vm['op']} == {Op.DIV} then
      {vm['stack']}[{vm['a']}] = {vm['k']}({vm['b']}) / {vm['k']}({vm['c']})
    elseif {vm['op']} == {Op.MOD} then
      {vm['stack']}[{vm['a']}] = {vm['k']}({vm['b']}) % {vm['k']}({vm['c']})
    elseif {vm['op']} == {Op.POW} then
      {vm['stack']}[{vm['a']}] = {vm['k']}({vm['b']}) ^ {vm['k']}({vm['c']})
    elseif {vm['op']} == {Op.IDIV} then
      {vm['stack']}[{vm['a']}] = {vm['k']}({vm['b']}) // {vm['k']}({vm['c']})
    elseif {vm['op']} == {Op.BAND} then
      {vm['stack']}[{vm['a']}] = {vm['k']}({vm['b']}) & {vm['k']}({vm['c']})
    elseif {vm['op']} == {Op.BOR} then
      {vm['stack']}[{vm['a']}] = {vm['k']}({vm['b']}) | {vm['k']}({vm['c']})
    elseif {vm['op']} == {Op.BXOR} then
      {vm['stack']}[{vm['a']}] = {vm['k']}({vm['b']}) ~ {vm['k']}({vm['c']})
    elseif {vm['op']} == {Op.SHL} then
      {vm['stack']}[{vm['a']}] = {vm['k']}({vm['b']}) << {vm['k']}({vm['c']})
    elseif {vm['op']} == {Op.SHR} then
      {vm['stack']}[{vm['a']}] = {vm['k']}({vm['b']}) >> {vm['k']}({vm['c']})
    elseif {vm['op']} == {Op.UNM} then
      {vm['stack']}[{vm['a']}] = -{vm['stack']}[{vm['b']}]
    elseif {vm['op']} == {Op.NOT} then
      {vm['stack']}[{vm['a']}] = not {vm['stack']}[{vm['b']}]
    elseif {vm['op']} == {Op.LEN} then
      {vm['stack']}[{vm['a']}] = #{vm['stack']}[{vm['b']}]
    elseif {vm['op']} == {Op.BNOT} then
      {vm['stack']}[{vm['a']}] = ~{vm['stack']}[{vm['b']}]
    elseif {vm['op']} == {Op.CONCAT} then
      local {vm['top']} = ""
      for {vm['i']}={vm['b']},{vm['c']} do {vm['top']}={vm['top']}..tostring({vm['stack']}[{vm['i']}]) end
      {vm['stack']}[{vm['a']}] = {vm['top']}
    elseif {vm['op']} == {Op.JMP} then
      {vm['pc']} = {vm['pc']} + {vm['sbx']}
    elseif {vm['op']} == {Op.EQ} then
      if ({vm['k']}({vm['b']}) == {vm['k']}({vm['c']})) ~= ({vm['a']}~=0) then {vm['pc']}={vm['pc']}+1 end
    elseif {vm['op']} == {Op.LT} then
      if ({vm['k']}({vm['b']}) < {vm['k']}({vm['c']})) ~= ({vm['a']}~=0) then {vm['pc']}={vm['pc']}+1 end
    elseif {vm['op']} == {Op.LE} then
      if ({vm['k']}({vm['b']}) <= {vm['k']}({vm['c']})) ~= ({vm['a']}~=0) then {vm['pc']}={vm['pc']}+1 end
    elseif {vm['op']} == {Op.TEST} then
      if (not not {vm['stack']}[{vm['a']}]) == ({vm['c']}~=0) then {vm['pc']}={vm['pc']}+1 end
    elseif {vm['op']} == {Op.TESTSET} then
      if (not not {vm['stack']}[{vm['b']}]) == ({vm['c']}~=0) then
        {vm['stack']}[{vm['a']}] = {vm['stack']}[{vm['b']}]
      else
        {vm['pc']} = {vm['pc']} + 1
      end
    elseif {vm['op']} == {Op.CALL} then
      local {vm['func']} = {vm['stack']}[{vm['a']}]
      local {vm['args']} = {{}}
      for {vm['i']}=1,{vm['b']}-1 do {vm['args']}[{vm['i']}]={vm['stack']}[{vm['a']}+{vm['i']}] end
      local {vm['results']} = {{{vm['func']}(table.unpack({vm['args']}))}}
      for {vm['i']}=1,{vm['c']}-1 do {vm['stack']}[{vm['a']}+{vm['i']}-1]={vm['results']}[{vm['i']}] end
    elseif {vm['op']} == {Op.TAILCALL} then
      local {vm['func']} = {vm['stack']}[{vm['a']}]
      local {vm['args']} = {{}}
      for {vm['i']}=1,{vm['b']}-1 do {vm['args']}[{vm['i']}]={vm['stack']}[{vm['a']}+{vm['i']}] end
      return {vm['func']}(table.unpack({vm['args']}))
    elseif {vm['op']} == {Op.RETURN} then
      if {vm['b']} == 1 then return end
      local {vm['results']} = {{}}
      for {vm['i']}=1,{vm['b']}-1 do {vm['results']}[{vm['i']}]={vm['stack']}[{vm['a']}+{vm['i']}-1] end
      return table.unpack({vm['results']})
    elseif {vm['op']} == {Op.FORPREP} then
      {vm['stack']}[{vm['a']}] = {vm['stack']}[{vm['a']}] - {vm['stack']}[{vm['a']}+2]
      {vm['pc']} = {vm['pc']} + {vm['sbx']}
    elseif {vm['op']} == {Op.FORLOOP} then
      {vm['stack']}[{vm['a']}] = {vm['stack']}[{vm['a']}] + {vm['stack']}[{vm['a']}+2]
      if {vm['stack']}[{vm['a']}+2] > 0 then
        if {vm['stack']}[{vm['a']}] <= {vm['stack']}[{vm['a']}+1] then
          {vm['pc']} = {vm['pc']} + {vm['sbx']}
          {vm['stack']}[{vm['a']}+3] = {vm['stack']}[{vm['a']}]
        end
      else
        if {vm['stack']}[{vm['a']}] >= {vm['stack']}[{vm['a']}+1] then
          {vm['pc']} = {vm['pc']} + {vm['sbx']}
          {vm['stack']}[{vm['a']}+3] = {vm['stack']}[{vm['a']}]
        end
      end
    elseif {vm['op']} == {Op.TFORLOOP} then
      local {vm['func']}={vm['stack']}[{vm['a']}]
      local {vm['results']}={{{vm['func']}({vm['stack']}[{vm['a']}+1],{vm['stack']}[{vm['a']}+2])}}
      if {vm['results']}[1]~=nil then
        {vm['stack']}[{vm['a']}+2]={vm['results']}[1]
        for {vm['i']}=1,{vm['c']} do {vm['stack']}[{vm['a']}+2+{vm['i']}]={vm['results']}[{vm['i']}] end
      else
        {vm['pc']}={vm['pc']}+1
      end
    elseif {vm['op']} == {Op.CLOSURE} then
      local {vm['top']}={vm['protos']}[{vm['bx']}+1]
      {vm['stack']}[{vm['a']}]=function(...)
        return {vm['execute']}({vm['top']},{vm['env']},...)
      end
    elseif {vm['op']} == {Op.SELF} then
      {vm['stack']}[{vm['a']}+1]={vm['stack']}[{vm['b']}]
      {vm['stack']}[{vm['a']}]={vm['stack']}[{vm['b']}][{vm['k']}({vm['c']})]
    elseif {vm['op']} == {Op.SETLIST} then
      for {vm['i']}=1,{vm['b']} do
        {vm['stack']}[{vm['a']}][({vm['c']}-1)*50+{vm['i']}]={vm['stack']}[{vm['a']}+{vm['i']}]
      end
    elseif {vm['op']} == {Op.VARARG} then
      local {vm['top']}={vm['stack']}[0] or {{}}
      for {vm['i']}=1,{vm['b']}-1 do {vm['stack']}[{vm['a']}+{vm['i']}-1]={vm['top']}[{vm['proto']}.{vm['params']}+{vm['i']}] end
    end
  end
end
-- [[ BYTECODE ]]
local {vm['proto']} = {bytecode}
-- [[ ENTRY POINT ]]
local {vm['func']} = function(...)
  return {vm['execute']}({vm['proto']}, getfenv and getfenv() or _G, ...)
end
{vm['func']}()
"""
    return lua_vm
