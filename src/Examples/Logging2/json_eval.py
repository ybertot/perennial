class Module(object):
  def __init__(self, j):
    self.types = {}
    self.decls = {}
    self.constructors = {}

    self.modname = j['name']

    for d in j['declarations']:
      self._annotate_globals(d)
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

  def _annotate_globals(self, expr):
    if type(expr) == dict:
      if expr.get('what') == 'expr:global':
        expr['mod'] = self
      if expr.get('what') == 'type:glob':
        expr['mod'] = self
      if expr.get('what') == 'expr:constructor':
        expr['mod'] = self
      for k, v in expr.items():
        self._annotate_globals(v)

    if type(expr) == list:
      for v in expr:
        self._annotate_globals(v)

  def redefine_term(self, n, val):
    self.decls[n]['value'] = val

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

  def reduce(self, expr):
    while True:
      if expr['what'] == 'expr:apply':
        f = self.reduce(expr['func'])
        if f['what'] == 'expr:lambda':
          args = expr['args']
          res = apply(f, args[0])
          expr = {
            'what': 'expr:apply',
            'args': args[1:],
            'func': res,
          }
          if len(expr['args']) == 0:
            expr = expr['func']
          continue

      if expr['what'] == 'expr:coerce':
        expr = expr['value']
        continue

      if expr['what'] == 'expr:global':
        mod, name = self.scope_name(expr['name'], expr['mod'])
        expr, _ = mod.get_term(name)
        continue

      if expr['what'] == 'type:glob':
        mod, name = self.scope_name(expr['name'], expr['mod'])
        res = mod.get_type(name)
        res = {k: v for k, v in res.items()}
        res['args'] = res.get('args', []) + expr['args']
        expr = res
        continue

      if expr['what'] == 'decl:ind':
        args = expr.get('args', [])
        if len(args) > 0:
          arg = args[0]
          argname = expr['argnames'][0]
          res = {
            'what': expr['what'],
            'constructors': subst_what(expr['constructors'], 'type:var', argname, arg),
            'argnames': expr['argnames'][1:],
            'args': expr['args'][1:],
            'name': expr['name'],
          }
          expr = res
          continue

      ## No reductions possible
      return expr

  def scope_name(self, name, module_context):
    if '.' in name:
      modname, localname = name.split('.')
      return self.modules[modname], localname
    else:
      return module_context, name

def subst_what(expr, what, argname, argval):
  if type(expr) == dict:
    if expr.get('what') == what and expr['name'] == argname:
      return argval
    return {k: subst_what(v, what, argname, argval) for k, v in expr.items()}

  if type(expr) == list:
    return [subst_what(v, what, argname, argval) for v in expr]

  return expr

def apply(lam, argval):
  if lam['what'] != 'expr:lambda':
    raise Exception("apply on", lam['what'])

  argname = lam['argnames'][0]
  res = {
    'what': 'expr:lambda',
    'argnames': lam['argnames'][1:],
    'body': subst_what(lam['body'], 'expr:rel', argname, argval),
  }

  if len(res['argnames']) == 0:
    res = res['body']

  return res
