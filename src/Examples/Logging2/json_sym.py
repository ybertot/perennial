import collections
import z3

class SymbolicJSON(object):
  def __init__(self, context):
    self.context = context
    self.base_types = {}

  def register_base_type(self, name, z3sort_lam):
    self.base_types[name] = z3sort_lam

  def z3_sort(self, typeexpr):
    ## Hard-coded Z3 correspondence for some types
    base_lam = self.base_types.get(typeexpr['name'])
    if base_lam is not None:
      return base_lam(typeexpr['args'])

    typeexpr = self.context.reduce(typeexpr)

    datatype = z3.Datatype(str(typeexpr['name']))
    for c in typeexpr['constructors']:
      cname = str(c['name'])
      datatype.declare(cname, *[(cname + '_%d' % idx, self.z3_sort(argtype))
                                for (idx, argtype) in enumerate(c['argtypes'])])

    t = datatype.create()
    return t

def constructor_by_name(self, sort, cname):
  for i in range(0, sort.num_constructors()):
    if sort.constructor(i).name() == cname:
      return i
  raise Exception("Unknown constructor", sort, cname)
