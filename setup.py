import os
from distutils.extension import Extension
from distutils.core import setup

# Keep this variable synchronized with DATA_DIR in Makefile
datadir = "share/pyon/"

testcases = ['testcases/' + f for f in os.listdir('testcases')]

operators_ext = Extension('pyon.ast.operators',
                          ['src/pyon/ast/operators.c'])

setup(name = 'Pyon',
      version = '0.1',
      description = 'Pyon compiler',
      packages = ['pyon', 'pyon.ast', 'pyon.tests', 'pyon.types', 'pyon.ssa'],
      data_files =
	[("share/pyon/library", ["library/PyonBuiltin.glu"])] +
	[("share/pyon/testcases", testcases)],
      package_dir = {'': 'src'},
      ext_modules = [operators_ext])
