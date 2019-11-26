import json
import json_eval

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

res = jc.reduce(expr, m)
print res
