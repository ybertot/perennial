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

getattr_step, _ = m.get_term("getattr_step")

arg = 5

expr = {
  'what': 'expr:apply',
  'args': [arg],
  'func': getattr_step,
}

res = jc.reduce(expr)
print res

stateType = m.get_type("state")

sym = json_sym.SymbolicJSON(jc)
sym.register_base_type("nat", lambda args: z3.IntSort())
sym.register_base_type("string", lambda args: z3.StringSort())
sym.register_base_type("gmap", lambda args: z3.ArraySort(sym.z3_sort(args[0]), sym.z3_sort(args[1])))
sym.register_base_type("buf", lambda args: z3.SeqSort(z3.BitVecSort(8)))
sym.register_base_type("list", lambda args: z3.SeqSort(sym.z3_sort(args[0])))

z3sort = sym.z3_sort(stateType)
print z3sort
