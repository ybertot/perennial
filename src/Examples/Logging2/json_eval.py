class Module(object):
  def __init__(self, j):
    self.types = {}
    self.decls = {}
    self.constructors = {}

    self.modname = j['name']

    for d in j['declarations']:
      if d['what'] == 'decl:ind':
        self.types[d['name']] = d
        for c in d['constructors']:
          self.constructors[c['name']] = {
            'typename': d['name'],
            'argtypes': c['argtypes'],
          }
      elif d['what'] == 'decl:term':
        self.decls[d['name']] = d
      elif d['what'] == 'decl:type':
        self.types[d['name']] = d['value']
      elif d['what'] == 'decl:fixgroup':
        ## Not handled yet
        pass
      else:
        raise Exception("Unknown declaration", d['what'])

  def get_type(self, n):
    return self.types[n]

  def get_term(self, n):
    t = self.decls[n]
    return t['value'], t['type']

  def get_constructor(self, n):
    return self.constructors[n]

class Context(object):
  def __init__(self):
    self.modules = {}

  def load(self, j):
    m = Module(j)
    self.modules[m.modname] = m

  def get_module(self, n):
    return self.modules[n]

  def reduce(self, expr, module_context):
    while True:
      if expr['what'] == 'expr:apply':
        f = expr['func']
        args = expr['args']
        for arg in args:
          f = self.reduce(f, module_context)
          f = apply(f, arg)
        expr = f
        continue

      if expr['what'] == 'expr:global':
        mod, name = self.scope_name(expr['name'], module_context)
        expr, _ = mod.get_term(name)
        continue

      ## No reductions possible
      return expr

  def scope_name(self, name, module_context):
    if '.' in name:
      modname, localname = name.split('.')
      return self.modules[modname], localname
    else:
      return module_context, name

def subst_rel(expr, argname, argval):
  if type(expr) == dict:
    if expr['what'] == 'expr:rel' and expr['name'] == argname:
      return argval
    return {k: subst_rel(v, argname, argval) for k, v in expr.items()}

  if type(expr) == list:
    return [subst_rel(v, argname, argval) for v in expr]

  return expr

def apply(lam, argval):
  if lam['what'] != 'expr:lambda':
    raise Exception("apply on", lam['what'])

  argname = lam['argnames'][0]
  res = {
    'what': 'expr:lambda',
    'argnames': lam['argnames'][1:],
    'body': subst_rel(lam['body'], argname, argval),
  }

  if len(res['argnames']) == 0:
    res = res['body']

  return res
