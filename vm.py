"""
VM Obfuscator - Stack-based VM with opcode shuffling and string obfuscation.
Inspired by YAJU True VM Obfuscator v4.2 (Lua5.1/Luau compatible).
"""
import random
import string
from parser import *

# ── Opcodes ────────────────────────────────────────────────────────────────
class Op:
    PUSH_NIL    = 1
    PUSH_TRUE   = 2
    PUSH_FALSE  = 3
    PUSH_NUM    = 4
    PUSH_STR    = 5
    PUSH_VAR    = 6
    PUSH_GLOBAL = 7
    POP         = 8
    DUP         = 9
    SWAP        = 10
    ADJUST      = 11
    SET_LOCAL   = 12
    SET_GLOBAL  = 13
    NEW_TABLE   = 14
    GET_TABLE   = 15
    SET_TABLE   = 16
    GET_FIELD   = 17
    SET_FIELD   = 18
    ADD         = 19
    SUB         = 20
    MUL         = 21
    DIV         = 22
    MOD         = 23
    POW         = 24
    IDIV        = 25
    UNM         = 26
    NOT         = 27
    LEN         = 28
    BAND        = 29
    BOR         = 30
    BXOR        = 31
    BNOT        = 32
    SHL         = 33
    SHR         = 34
    CONCAT      = 35
    EQ          = 36
    NEQ         = 37
    LT          = 38
    GT          = 39
    LEQ         = 40
    GEQ         = 41
    AND_JMP     = 42
    OR_JMP      = 43
    JMP         = 44
    JMP_FALSE   = 45
    JMP_TRUE    = 46
    CALL        = 47
    RETURN      = 48
    CLOSURE     = 49
    SETLIST     = 50
    FORPREP     = 51
    FORLOOP     = 52
    GFORPREP    = 53
    GFORLOOP    = 54
    ENTER_SCOPE = 55
    LEAVE_SCOPE = 56
    PUSH_VARARG = 57
    TAILCALL    = 58

MAX_OP = 58

# ── Name / identifier generation ──────────────────────────────────────────
_used_names = set()

def obfuscate_name(length=None):
    if length is None:
        length = random.randint(10, 16)
    first_chars = ['l', 'I', 'O']
    rest_chars  = ['l', 'I', '1', 'O', '0']
    while True:
        name = random.choice(first_chars) + ''.join(random.choices(rest_chars, k=length - 1))
        if name not in _used_names:
            _used_names.add(name)
            return name

def reset_names():
    _used_names.clear()

# ── Number obfuscation ────────────────────────────────────────────────────
def obf_number(n):
    n = int(n)
    if n == 0:
        return "0"
    r = random.randint(0, 2)
    if r == 0:
        a = random.randint(2, 40)
        b = n // a
        c = n - a * b
        return f"({a}*{b}+{c})"
    elif r == 1:
        o = random.randint(5, 80)
        return f"({n+o}-{o})"
    else:
        f = random.randint(2, 6)
        q = n // f
        c = n - f * q
        return f"({f}*{q}+{c})"

# ── String obfuscation ────────────────────────────────────────────────────
def hide_str(s):
    if not s:
        return '""'
    key = random.randint(3, 52)
    enc = []
    for i, ch in enumerate(s.encode('utf-8', errors='replace')):
        enc.append((ch + key + (i % 7) * 3) % 255 + 1)
    vt = obfuscate_name()
    vr = obfuscate_name()
    vi = obfuscate_name()
    enc_str = ','.join(str(x) for x in enc)
    return (
        f"(function()"
        f"local {vt}={{{enc_str}}};"
        f"local {vr}={{}};"
        f"for {vi}=1,#{vt} do "
        f"{vr}[{vi}]=string.char(({vt}[{vi}]-1-{key}-{vi}%7*3+510)%255)"
        f" end;"
        f"return table.concat({vr})"
        f"end)()"
    )

# ── Bytecode instruction ──────────────────────────────────────────────────
class Instr:
    def __init__(self, op, arg=0):
        self.op  = op
        self.arg = arg

# ── Proto (function prototype) ────────────────────────────────────────────
class Proto:
    def __init__(self):
        self.code   = []
        self.consts = []
        self.names  = []
        self.funcs  = []
        self.params = 0

    def add_const(self, v):
        try:
            return self.consts.index(v)
        except ValueError:
            self.consts.append(v)
            return len(self.consts) - 1

    def add_name(self, n):
        try:
            return self.names.index(n)
        except ValueError:
            self.names.append(n)
            return len(self.names) - 1

    def emit(self, op, arg=0):
        self.code.append(Instr(op, arg))
        return len(self.code) - 1

    def patch(self, idx, arg):
        self.code[idx].arg = arg

    def here(self):
        return len(self.code)

# ── Stack-based Compiler ──────────────────────────────────────────────────
class Compiler:
    def __init__(self):
        self.proto  = None
        self.locals = []
        self.scopes = []

    def compile(self, ast):
        self.proto  = Proto()
        self.locals = []
        self.scopes = []
        self._block(ast)
        self.proto.emit(Op.RETURN, 0)
        return self.proto

    def _is_local(self, name):
        return name in self.locals

    def _push_scope(self):
        self.scopes.append(len(self.locals))
        self.proto.emit(Op.ENTER_SCOPE)

    def _pop_scope(self):
        saved = self.scopes.pop()
        del self.locals[saved:]
        self.proto.emit(Op.LEAVE_SCOPE)

    def _N(self, name):
        return self.proto.add_name(name)

    def _K(self, val):
        return self.proto.add_const(val)

    def _push_var(self, name):
        if self._is_local(name):
            self.proto.emit(Op.PUSH_VAR, self._N(name))
        else:
            self.proto.emit(Op.PUSH_GLOBAL, self._N(name))

    def _set_var(self, name):
        if self._is_local(name):
            self.proto.emit(Op.SET_LOCAL, self._N(name))
        else:
            self.proto.emit(Op.SET_GLOBAL, self._N(name))

    def _block(self, block):
        self._push_scope()
        for stmt in block.stmts:
            self._stmt(stmt)
        if block.ret:
            self._return(block.ret)
        self._pop_scope()

    def _stmt(self, stmt):
        if   isinstance(stmt, AssignStmt):    self._assign(stmt)
        elif isinstance(stmt, LocalStmt):     self._local(stmt)
        elif isinstance(stmt, CallStmt):      self._call_stmt(stmt)
        elif isinstance(stmt, DoStmt):        self._block(stmt.block)
        elif isinstance(stmt, WhileStmt):     self._while(stmt)
        elif isinstance(stmt, RepeatStmt):    self._repeat(stmt)
        elif isinstance(stmt, IfStmt):        self._if(stmt)
        elif isinstance(stmt, ForNumStmt):    self._fornum(stmt)
        elif isinstance(stmt, ForInStmt):     self._forin(stmt)
        elif isinstance(stmt, FuncStmt):      self._func_stmt(stmt)
        elif isinstance(stmt, LocalFuncStmt): self._local_func(stmt)
        elif isinstance(stmt, ReturnStmt):    self._return(stmt)
        elif isinstance(stmt, BreakStmt):     pass
        elif isinstance(stmt, GotoStmt):      pass
        elif isinstance(stmt, LabelStmt):     pass

    def _return(self, stmt):
        n = len(stmt.values)
        for v in stmt.values:
            self._expr(v)
        self.proto.emit(Op.RETURN, n)

    def _assign(self, stmt):
        n_lhs = len(stmt.targets)
        n_rhs = len(stmt.values)
        for v in stmt.values:
            self._expr(v)
        if n_rhs != n_lhs:
            self.proto.emit(Op.ADJUST, n_lhs)
        for tgt in reversed(stmt.targets):
            self._assign_target(tgt)

    def _assign_target(self, tgt):
        if isinstance(tgt, NameExpr):
            self._set_var(tgt.name)
        elif isinstance(tgt, FieldExpr):
            self._expr(tgt.table)
            self.proto.emit(Op.SET_FIELD, self._N(tgt.field))
        elif isinstance(tgt, IndexExpr):
            self._expr(tgt.table)
            self._expr(tgt.key)
            self.proto.emit(Op.SET_TABLE)

    def _local(self, stmt):
        n = len(stmt.names)
        for i, nm in enumerate(stmt.names):
            if i < len(stmt.values):
                self._expr(stmt.values[i])
            else:
                self.proto.emit(Op.PUSH_NIL)
        if len(stmt.values) != n:
            self.proto.emit(Op.ADJUST, n)
        for nm in reversed(stmt.names):
            self.locals.append(nm)
            self.proto.emit(Op.SET_LOCAL, self._N(nm))

    def _call_stmt(self, stmt):
        self._expr(stmt.expr)
        self.proto.emit(Op.POP)

    def _while(self, stmt):
        ls = self.proto.here()
        self._expr(stmt.cond)
        jf = self.proto.emit(Op.JMP_FALSE, 0)
        self._block(stmt.block)
        self.proto.emit(Op.JMP, ls - self.proto.here() - 1)
        self.proto.patch(jf, self.proto.here() - jf)

    def _repeat(self, stmt):
        ls = self.proto.here()
        self._block(stmt.block)
        self._expr(stmt.cond)
        self.proto.emit(Op.JMP_FALSE, ls - self.proto.here() - 1)

    def _if(self, stmt):
        self._expr(stmt.cond)
        jf = self.proto.emit(Op.JMP_FALSE, 0)
        self._block(stmt.then_block)
        exits = [self.proto.emit(Op.JMP, 0)]
        self.proto.patch(jf, self.proto.here() - jf)
        for (ec, eb) in stmt.elseifs:
            self._expr(ec)
            jf2 = self.proto.emit(Op.JMP_FALSE, 0)
            self._block(eb)
            exits.append(self.proto.emit(Op.JMP, 0))
            self.proto.patch(jf2, self.proto.here() - jf2)
        if stmt.else_block:
            self._block(stmt.else_block)
        for e in exits:
            self.proto.patch(e, self.proto.here() - e)

    def _fornum(self, stmt):
        self._expr(stmt.start)
        self._expr(stmt.stop)
        if stmt.step:
            self._expr(stmt.step)
        else:
            self.proto.emit(Op.PUSH_NUM, self._K(1.0))
        fp = self.proto.emit(Op.FORPREP, 0)
        self.locals.append(stmt.name)
        lb = self.proto.here()
        self._block(stmt.block)
        self.proto.emit(Op.FORLOOP, lb - self.proto.here() - 1)
        self.proto.patch(fp, self.proto.here() - fp)
        self.locals.remove(stmt.name)

    def _forin(self, stmt):
        for it in stmt.iters:
            self._expr(it)
        for _ in range(3 - len(stmt.iters)):
            self.proto.emit(Op.PUSH_NIL)
        gfp = self.proto.emit(Op.GFORPREP, 0)
        for nm in stmt.names:
            self.locals.append(nm)
        lb = self.proto.here()
        self._block(stmt.block)
        self.proto.emit(Op.GFORLOOP, lb - self.proto.here() - 1)
        self.proto.patch(gfp, self.proto.here() - gfp)
        for nm in stmt.names:
            if nm in self.locals:
                self.locals.remove(nm)

    def _func_stmt(self, stmt):
        fi = self._compile_func(stmt.params, stmt.has_vararg, stmt.block)
        self.proto.emit(Op.CLOSURE, fi)
        name = '.'.join(stmt.name)
        if stmt.method:
            name += ':' + stmt.method
        self._set_var(name)

    def _local_func(self, stmt):
        self.locals.append(stmt.name)
        fi = self._compile_func(stmt.params, stmt.has_vararg, stmt.block)
        self.proto.emit(Op.CLOSURE, fi)
        self.proto.emit(Op.SET_LOCAL, self._N(stmt.name))

    def _compile_func(self, params, has_vararg, block):
        sub = Compiler()
        sub.proto        = Proto()
        sub.proto.params = len(params)
        sub.locals       = list(params)
        sub.scopes       = []
        sub._block(block)
        sub.proto.emit(Op.RETURN, 0)
        self.proto.funcs.append(sub.proto)
        return len(self.proto.funcs) - 1

    def _expr(self, expr):
        if isinstance(expr, NumberExpr):
            v = float(expr.value.replace('_', ''))
            self.proto.emit(Op.PUSH_NUM, self._K(v))
        elif isinstance(expr, StringExpr):
            self.proto.emit(Op.PUSH_STR, self._K(expr.value))
        elif isinstance(expr, BoolExpr):
            self.proto.emit(Op.PUSH_TRUE if expr.value else Op.PUSH_FALSE)
        elif isinstance(expr, NilExpr):
            self.proto.emit(Op.PUSH_NIL)
        elif isinstance(expr, VarArgExpr):
            self.proto.emit(Op.PUSH_VARARG)
        elif isinstance(expr, NameExpr):
            self._push_var(expr.name)
        elif isinstance(expr, FieldExpr):
            self._expr(expr.table)
            self.proto.emit(Op.GET_FIELD, self._N(expr.field))
        elif isinstance(expr, IndexExpr):
            self._expr(expr.table)
            self._expr(expr.key)
            self.proto.emit(Op.GET_TABLE)
        elif isinstance(expr, BinOpExpr):
            self._binop(expr)
        elif isinstance(expr, UnOpExpr):
            self._unop(expr)
        elif isinstance(expr, CallExpr):
            self._call_expr(expr)
        elif isinstance(expr, MethodCallExpr):
            self._method_call(expr)
        elif isinstance(expr, FuncExpr):
            fi = self._compile_func(expr.params, expr.has_vararg, expr.block)
            self.proto.emit(Op.CLOSURE, fi)
        elif isinstance(expr, TableExpr):
            self._table(expr)

    def _binop(self, expr):
        op_map = {
            '+': Op.ADD, '-': Op.SUB, '*': Op.MUL, '/': Op.DIV,
            '%': Op.MOD, '^': Op.POW, '//': Op.IDIV, '..': Op.CONCAT,
            '&': Op.BAND, '|': Op.BOR, '~': Op.BXOR,
            '<<': Op.SHL, '>>': Op.SHR,
            '==': Op.EQ, '~=': Op.NEQ, '<': Op.LT, '>': Op.GT,
            '<=': Op.LEQ, '>=': Op.GEQ,
        }
        if expr.op == 'and':
            self._expr(expr.left)
            j = self.proto.emit(Op.AND_JMP, 0)
            self._expr(expr.right)
            self.proto.patch(j, self.proto.here() - j)
        elif expr.op == 'or':
            self._expr(expr.left)
            j = self.proto.emit(Op.OR_JMP, 0)
            self._expr(expr.right)
            self.proto.patch(j, self.proto.here() - j)
        else:
            self._expr(expr.left)
            self._expr(expr.right)
            self.proto.emit(op_map.get(expr.op, Op.ADD))

    def _unop(self, expr):
        op_map = {'-': Op.UNM, 'not': Op.NOT, '#': Op.LEN, '~': Op.BNOT}
        self._expr(expr.operand)
        self.proto.emit(op_map.get(expr.op, Op.UNM))

    def _call_expr(self, expr):
        self._expr(expr.func)
        for a in expr.args:
            self._expr(a)
        self.proto.emit(Op.CALL, len(expr.args))

    def _method_call(self, expr):
        self._expr(expr.obj)
        self.proto.emit(Op.DUP)
        self.proto.emit(Op.GET_FIELD, self._N(expr.method))
        self.proto.emit(Op.SWAP)
        for a in expr.args:
            self._expr(a)
        self.proto.emit(Op.CALL, len(expr.args) + 1)

    def _table(self, expr):
        self.proto.emit(Op.NEW_TABLE)
        idx = 0
        for field in expr.fields:
            if field.key is None:
                idx += 1
                self._expr(field.value)
                self.proto.emit(Op.SETLIST, idx)
            elif isinstance(field.key, StringExpr):
                self._expr(field.value)
                self.proto.emit(Op.SET_FIELD, self._N(field.key.value))
            else:
                self._expr(field.key)
                self._expr(field.value)
                self.proto.emit(Op.SET_TABLE)


# ── Opcode shuffling ──────────────────────────────────────────────────────
def make_opcode_map():
    pool = list(range(1, MAX_OP + 1))
    random.shuffle(pool)
    op2c = {}
    c2op = {}
    for orig, scr in enumerate(pool, 1):
        op2c[orig] = scr
        c2op[scr]  = orig
    return op2c, c2op

def remap_proto(proto, op2c):
    for ins in proto.code:
        ins.op = op2c.get(ins.op, ins.op)
    for sub in proto.funcs:
        remap_proto(sub, op2c)


# ── Serializer ────────────────────────────────────────────────────────────
def serialize_proto(proto):
    k_parts = []
    for c in proto.consts:
        if isinstance(c, str):
            k_parts.append(hide_str(c))
        elif isinstance(c, float):
            iv = int(c)
            if c == iv and abs(iv) < 10**12:
                k_parts.append(obf_number(iv))
            else:
                k_parts.append(repr(c))
        else:
            k_parts.append(str(c))

    n_parts = [hide_str(n) for n in proto.names]
    c_parts = [f"{{{obf_number(ins.op)},{obf_number(ins.arg)}}}" for ins in proto.code]
    f_parts = [serialize_proto(sub) for sub in proto.funcs]

    return (
        f"{{k={{{','.join(k_parts)}}},"
        f"n={{{','.join(n_parts)}}},"
        f"c={{{','.join(c_parts)}}},"
        f"f={{{','.join(f_parts)}}},"
        f"p={proto.params}}}"
    )


# ── VM runtime generator ──────────────────────────────────────────────────
def generate_vm_lua(proto):
    reset_names()

    op2c, c2op = make_opcode_map()
    remap_proto(proto, op2c)

    um_parts = [f"[{obf_number(s)}]={obf_number(o)}" for s, o in c2op.items()]
    um_str   = '{' + ','.join(um_parts) + '}'
    proto_str = serialize_proto(proto)

    def opc(name):
        return obf_number(op2c[getattr(Op, name)])

    vUM    = obfuscate_name()
    vPR    = obfuscate_name()
    vVM    = obfuscate_name()
    vF     = obfuscate_name()
    vST    = obfuscate_name()
    vEN    = obfuscate_name()
    vUV    = obfuscate_name()
    vPC    = obfuscate_name()
    vIN    = obfuscate_name()
    vOP    = obfuscate_name()
    vAR    = obfuscate_name()
    vSCOPE = obfuscate_name()
    vSET_L = obfuscate_name()
    vGET_L = obfuscate_name()
    vBIT   = obfuscate_name()
    vEntry = obfuscate_name()
    vK     = obfuscate_name()
    vN     = obfuscate_name()

    def pop():   return f"table.remove({vST})"
    def push(v): return f"{vST}[#{vST}+1]={v}"
    def top():   return f"{vST}[#{vST}]"

    def arith(opname, sym):
        va, vb = obfuscate_name(), obfuscate_name()
        return f"    elseif {vOP}=={opc(opname)} then local {vb}={pop()};local {va}={pop()};{push(f'{va}{sym}{vb}')}"

    def arith_fn(opname, fn):
        va, vb = obfuscate_name(), obfuscate_name()
        return f"    elseif {vOP}=={opc(opname)} then local {vb}={pop()};local {va}={pop()};{push(f'{vBIT}.{fn}({va},{vb})')}"

    def unary(opname, sym):
        va = obfuscate_name()
        return f"    elseif {vOP}=={opc(opname)} then local {va}={pop()};{push(f'{sym}{va}')}"

    def unary_fn(opname, fn):
        va = obfuscate_name()
        return f"    elseif {vOP}=={opc(opname)} then local {va}={pop()};{push(f'{vBIT}.{fn}({va})')}"

    def cmp(opname, sym):
        va, vb = obfuscate_name(), obfuscate_name()
        return f"    elseif {vOP}=={opc(opname)} then local {vb}={pop()};local {va}={pop()};{push(f'({va}{sym}{vb})')}"

    vv1=obfuscate_name(); vv2=obfuscate_name(); vv3=obfuscate_name()
    vs1=obfuscate_name(); vs2=obfuscate_name()
    vsl=obfuscate_name(); vsg=obfuscate_name()
    vgt_k=obfuscate_name(); vgt_t=obfuscate_name()
    vst_v=obfuscate_name(); vst_k=obfuscate_name(); vst_t=obfuscate_name()
    vgf_t=obfuscate_name()
    vsf_v=obfuscate_name(); vsf_t=obfuscate_name()
    vls_v=obfuscate_name(); vls_t=obfuscate_name()
    vajmp=obfuscate_name(); vojmp=obfuscate_name()
    vjf=obfuscate_name(); vjt=obfuscate_name()
    vfn=obfuscate_name(); vargs=obfuscate_name(); vres=obfuscate_name()
    vci=obfuscate_name(); vci2=obfuscate_name()
    vrv=obfuscate_name(); vri=obfuscate_name()
    vcls=obfuscate_name(); vcenv=obfuscate_name()
    vidiv_a=obfuscate_name(); vidiv_b=obfuscate_name()
    vfp_st=obfuscate_name(); vfp_lim=obfuscate_name(); vfp_stp=obfuscate_name()
    vfl_stp=obfuscate_name(); vfl_lim=obfuscate_name(); vfl_v=obfuscate_name()
    vgfp_c=obfuscate_name(); vgfp_s=obfuscate_name(); vgfp_i=obfuscate_name()
    vgfl_c=obfuscate_name(); vgfl_s=obfuscate_name(); vgfl_i=obfuscate_name()
    vgfl_r=obfuscate_name(); vgfl_j=obfuscate_name()

    lines = []
    def L(s): lines.append(s)

    L("(function()")
    L(f"local {vUM}={um_str}")
    L(f"local {vPR}={proto_str}")

    # Lua5.1/Luau compatible bit helpers
    L(f"local {vBIT}={{}}")
    L("do")
    L("  local function _and(a,b) local r=0;for i=0,31 do if math.floor(a/2^i)%2==1 and math.floor(b/2^i)%2==1 then r=r+2^i end end;return r end")
    L("  local function _or(a,b)  local r=0;for i=0,31 do if math.floor(a/2^i)%2==1 or  math.floor(b/2^i)%2==1 then r=r+2^i end end;return r end")
    L("  local function _xor(a,b) local r=0;for i=0,31 do local x=math.floor(a/2^i)%2;local y=math.floor(b/2^i)%2;if x~=y then r=r+2^i end end;return r end")
    L("  local function _not(a)   local r=0;for i=0,31 do if math.floor(a/2^i)%2==0 then r=r+2^i end end;return r end")
    L("  local function _shl(a,b) return math.floor(a*(2^b))%4294967296 end")
    L("  local function _shr(a,b) return math.floor(a/(2^b)) end")
    L(f"  {vBIT}.band=_and;{vBIT}.bor=_or;{vBIT}.bxor=_xor;{vBIT}.bnot=_not;{vBIT}.shl=_shl;{vBIT}.shr=_shr")
    L("end")

    L(f"local {vVM}")
    L(f"{vVM}=function({vF},{vST},{vEN},{vUV})")
    L(f"  {vST}={vST} or {{}}")
    L(f"  {vEN}={vEN} or _G")
    L(f"  {vUV}={vUV} or {{}}")
    L(f"  local {vK}={vF}.k")
    L(f"  local {vN}={vF}.n")
    L(f"  local {vPC}=1")
    L(f"  local {vSCOPE}={{{{}}}}")
    L(f"  local function {vSET_L}(nm,val)")
    L(f"    for _i=#{vSCOPE},1,-1 do if {vSCOPE}[_i][nm]~=nil then {vSCOPE}[_i][nm]=val;return end end")
    L(f"    {vSCOPE}[#{vSCOPE}][nm]=val")
    L( "  end")
    L(f"  local function {vGET_L}(nm)")
    L(f"    for _i=#{vSCOPE},1,-1 do local v={vSCOPE}[_i][nm];if v~=nil then return v end end")
    L( "  end")
    L( "  while true do")
    L(f"    local {vIN}={vF}.c[{vPC}]")
    L(f"    if not {vIN} then break end")
    L(f"    local {vOP}={vUM}[{vIN}[1]]")
    L(f"    local {vAR}={vIN}[2]")
    L(f"    {vPC}={vPC}+1")

    L(f"    if     {vOP}=={opc('PUSH_NIL')}    then {push('nil')}")
    L(f"    elseif {vOP}=={opc('PUSH_TRUE')}   then {push('true')}")
    L(f"    elseif {vOP}=={opc('PUSH_FALSE')}  then {push('false')}")
    L(f"    elseif {vOP}=={opc('PUSH_NUM')}    then {push(f'{vK}[{vAR}+1]')}")
    L(f"    elseif {vOP}=={opc('PUSH_STR')}    then {push(f'{vK}[{vAR}+1]')}")
    L(f"    elseif {vOP}=={opc('PUSH_VARARG')} then -- vararg noop")
    L(f"    elseif {vOP}=={opc('PUSH_VAR')}    then local {vv1}={vGET_L}({vN}[{vAR}+1]);{push(vv1)}")
    L(f"    elseif {vOP}=={opc('PUSH_GLOBAL')} then local {vv2}={vEN}[{vN}[{vAR}+1]];{push(vv2)}")
    L(f"    elseif {vOP}=={opc('POP')}         then {pop()}")
    L(f"    elseif {vOP}=={opc('DUP')}         then local {vv3}={top()};{push(vv3)}")
    L(f"    elseif {vOP}=={opc('SWAP')}        then local {vs1}={pop()};local {vs2}={pop()};{push(vs1)};{push(vs2)}")
    L(f"    elseif {vOP}=={opc('ADJUST')}      then while #{vST}<{vAR} do {push('nil')} end;while #{vST}>{vAR} do {pop()} end")
    L(f"    elseif {vOP}=={opc('SET_LOCAL')}   then local {vsl}={pop()};{vSET_L}({vN}[{vAR}+1],{vsl})")
    L(f"    elseif {vOP}=={opc('SET_GLOBAL')}  then local {vsg}={pop()};{vEN}[{vN}[{vAR}+1]]={vsg}")
    L(f"    elseif {vOP}=={opc('NEW_TABLE')}   then {push('{}')}")
    L(f"    elseif {vOP}=={opc('GET_TABLE')}   then local {vgt_k}={pop()};local {vgt_t}={pop()};{push(f'{vgt_t}[{vgt_k}]')}")
    L(f"    elseif {vOP}=={opc('SET_TABLE')}   then local {vst_v}={pop()};local {vst_k}={pop()};local {vst_t}={pop()};{vst_t}[{vst_k}]={vst_v}")
    L(f"    elseif {vOP}=={opc('GET_FIELD')}   then local {vgf_t}={pop()};{push(f'{vgf_t}[{vN}[{vAR}+1]]')}")
    L(f"    elseif {vOP}=={opc('SET_FIELD')}   then local {vsf_v}={pop()};local {vsf_t}={pop()};{vsf_t}[{vN}[{vAR}+1]]={vsf_v}")
    L(f"    elseif {vOP}=={opc('SETLIST')}     then local {vls_v}={pop()};local {vls_t}={vST}[#{vST}];{vls_t}[{vAR}]={vls_v}")

    L(arith('ADD', '+'))
    L(arith('SUB', '-'))
    L(arith('MUL', '*'))
    L(arith('DIV', '/'))
    L(arith('MOD', '%'))
    L(arith('POW', '^'))
    L(f"    elseif {vOP}=={opc('IDIV')} then local {vidiv_b}={pop()};local {vidiv_a}={pop()};{push(f'math.floor({vidiv_a}/{vidiv_b})')}")
    L(arith_fn('BAND', 'band'))
    L(arith_fn('BOR',  'bor'))
    L(arith_fn('BXOR', 'bxor'))
    L(arith_fn('SHL',  'shl'))
    L(arith_fn('SHR',  'shr'))
    L(arith('CONCAT', '..'))
    L(unary('UNM',  '-'))
    L(unary('NOT',  'not '))
    L(unary('LEN',  '#'))
    L(unary_fn('BNOT', 'bnot'))
    L(cmp('EQ',  '=='))
    L(cmp('NEQ', '~='))
    L(cmp('LT',  '<'))
    L(cmp('GT',  '>'))
    L(cmp('LEQ', '<='))
    L(cmp('GEQ', '>='))

    L(f"    elseif {vOP}=={opc('AND_JMP')} then local {vajmp}={top()};if not {vajmp} then {vPC}={vPC}+{vAR};{push(vajmp)} else {pop()} end")
    L(f"    elseif {vOP}=={opc('OR_JMP')}  then local {vojmp}={top()};if {vojmp} then {vPC}={vPC}+{vAR};{push(vojmp)} else {pop()} end")
    L(f"    elseif {vOP}=={opc('JMP')}       then {vPC}={vPC}+{vAR}")
    L(f"    elseif {vOP}=={opc('JMP_FALSE')} then local {vjf}={pop()};if not {vjf} then {vPC}={vPC}+{vAR} end")
    L(f"    elseif {vOP}=={opc('JMP_TRUE')}  then local {vjt}={pop()};if {vjt} then {vPC}={vPC}+{vAR} end")

    L(f"    elseif {vOP}=={opc('CALL')} then")
    L(f"      local {vargs}={{}}")
    L(f"      for {vci}=1,{vAR} do table.insert({vargs},1,{pop()}) end")
    L(f"      local {vfn}={pop()}")
    L(f"      local {vres}={{{vfn}(table.unpack and table.unpack({vargs}) or unpack({vargs}))}}")
    L(f"      for {vci2}=1,#{vres} do {push(f'{vres}[{vci2}]')} end")

    L(f"    elseif {vOP}=={opc('TAILCALL')} then")
    L(f"      local {vargs}={{}}")
    L(f"      for {vci}=1,{vAR} do table.insert({vargs},1,{pop()}) end")
    L(f"      local {vfn}={pop()}")
    L(f"      return {vfn}(table.unpack and table.unpack({vargs}) or unpack({vargs}))")

    L(f"    elseif {vOP}=={opc('RETURN')} then")
    L(f"      local {vrv}={{}}")
    L(f"      for {vri}=1,{vAR} do table.insert({vrv},1,{pop()}) end")
    L(f"      return table.unpack and table.unpack({vrv}) or unpack({vrv})")

    L(f"    elseif {vOP}=={opc('CLOSURE')} then")
    L(f"      local {vcls}={vF}.f[{vAR}+1]")
    L(f"      local {vcenv}={vEN}")
    L(f"      {push(f'(function(...) return {vVM}({vcls},{{}},{vcenv},{{}}) end)')}")

    L(f"    elseif {vOP}=={opc('ENTER_SCOPE')} then {vSCOPE}[#{vSCOPE}+1]={{}}")
    L(f"    elseif {vOP}=={opc('LEAVE_SCOPE')} then {vSCOPE}[#{vSCOPE}]=nil")

    L(f"    elseif {vOP}=={opc('FORPREP')} then")
    L(f"      local {vfp_stp}={pop()};local {vfp_lim}={pop()};local {vfp_st}={pop()}")
    L(f"      {push(vfp_st)};{push(vfp_lim)};{push(vfp_stp)}")
    L(f"      if ({vfp_stp}>0 and {vfp_st}>{vfp_lim}) or ({vfp_stp}<=0 and {vfp_st}<{vfp_lim}) then {vPC}={vPC}+{vAR} end")

    L(f"    elseif {vOP}=={opc('FORLOOP')} then")
    L(f"      local {vfl_stp}={vST}[#{vST}];local {vfl_lim}={vST}[#{vST}-1];local {vfl_v}={vST}[#{vST}-2]")
    L(f"      {vfl_v}={vfl_v}+{vfl_stp};{vST}[#{vST}-2]={vfl_v}")
    L(f"      if ({vfl_stp}>0 and {vfl_v}<={vfl_lim}) or ({vfl_stp}<=0 and {vfl_v}>={vfl_lim}) then {vPC}={vPC}+{vAR} end")

    L(f"    elseif {vOP}=={opc('GFORPREP')} then")
    L(f"      local {vgfp_c}={pop()};local {vgfp_s}={pop()};local {vgfp_i}={pop()}")
    L(f"      {push(vgfp_i)};{push(vgfp_s)};{push(vgfp_c)}")

    L(f"    elseif {vOP}=={opc('GFORLOOP')} then")
    L(f"      local {vgfl_c}={vST}[#{vST}];local {vgfl_s}={vST}[#{vST}-1];local {vgfl_i}={vST}[#{vST}-2]")
    L(f"      local {vgfl_r}={{{vgfl_i}({vgfl_s},{vgfl_c})}}")
    L(f"      if {vgfl_r}[1]~=nil then")
    L(f"        {vST}[#{vST}]={vgfl_r}[1]")
    L(f"        for {vgfl_j}=#{vgfl_r},1,-1 do {push(f'{vgfl_r}[{vgfl_j}]')} end")
    L(f"        {vPC}={vPC}+{vAR}")
    L( "      end")

    L( "    end")
    L( "  end")
    L( "end")

    L(f"local {vEntry}=function()")
    L(f"  {vVM}({vPR},{{}},_G,{{}})")
    L( "end")
    L(f"{vEntry}()")
    L( "end)()")

    return '\n'.join(lines)
