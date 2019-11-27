## ahead of time:
##   export PYTHONPATH=/home/nickolai/refsrc/z3/build/python

import json
import json_eval
import json_sym
import z3

with open('NFS3API.json') as f:
  code = f.read()
  j = json.loads(code)

jc = json_eval.Context()
jc.load(j)

m = jc.get_module('Main')

stateType = m.get_type("state")

sym = json_sym.SymbolicJSON(jc)
sym.register_base_type("nat", lambda args: z3.IntSort())
sym.register_base_type("string", lambda args: z3.StringSort())
sym.register_base_type("gmap", lambda args: z3.ArraySort(sym.z3_sort(args[0]),
  sym.z3_sort({
    'what': 'type:glob',
    'name': 'option',
    'args': [args[1]],
    'mod': m,
  })))
sym.register_base_type("buf", lambda args: z3.SeqSort(z3.BitVecSort(8)))
sym.register_base_type("list", lambda args: z3.SeqSort(sym.z3_sort(args[0])))
sym.register_base_type("fh", lambda args: z3.IntSort())
sym.register_base_type("uint32", lambda args: z3.BitVecSort(32))
sym.register_base_type("uint64", lambda args: z3.BitVecSort(64))

### Fix later
sym.register_base_type("fileid", lambda args: z3.BitVecSort(64))
sym.register_base_type("createverf", lambda args: z3.BitVecSort(64))
sym.register_base_type("writeverf", lambda args: z3.BitVecSort(64))

sym.set_bool_type(m.get_type("bool"))

m.redefine_term('gmap_lookup', {
  'what': 'expr:lambda',
  'argnames': ['unused0', 'unused1'],
  'body': {
    'what': 'expr:special',
    'id': 'gmap_lookup',
  },
})
m.redefine_term('len_buf', {
  'what': 'expr:special',
  'id': 'len_buf',
})
m.redefine_term('u32_zero', {
  'what': 'expr:special',
  'id': 'u32_zero',
})
m.redefine_term('u64_zero', {
  'what': 'expr:special',
  'id': 'u64_zero',
})

stateSort = sym.z3_sort(stateType)
s0 = z3.Const('s0', stateSort)


getattr_step, _ = m.get_term("getattr_step")

arg = z3.Int('fh')

expr = {
  'what': 'expr:apply',
  'args': [arg],
  'func': getattr_step,
}

getattr_step_fh = jc.reduce(expr)

s1, res = sym.proc(getattr_step_fh, s0)
print s1
print res

ERR_PERM = res.sort().accessor(1, 1)(res).sort().constructor(0)()

s = z3.Solver()
# s.add(s0 != s1)
# s.add(res.sort().recognizer(0)(res))
s.add(res.sort().recognizer(1)(res))
s.add(res.sort().accessor(1, 1)(res) == ERR_PERM)
print 'Check:', s.check()
