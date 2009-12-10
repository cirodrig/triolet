from distutils.extension import Extension
from distutils.core import setup

# This flag depends on what versions of Python and Haskell get along.
# Use 'False' if possible.
#BUILD_32 = True
#
#if BUILD_32:
#    extra_compile_args = extra_link_args = ['-m32']
#else:
#    extra_compile_args = extra_link_args = []

operators_ext = Extension('pyon.ast.operators',
                          ['src/pyon/ast/operators.c'])
#                          extra_compile_args = extra_compile_args,
#                          extra_link_args = extra_link_args)

setup(name = 'Pyon',
      version = '0.1',
      description = 'Pyon compiler',
      packages = ['pyon', 'pyon.ast', 'pyon.tests'],
      package_data = {'pyon.tests' : ['sources/*.py']},
      package_dir = {'': 'src'},
      ext_modules = [operators_ext])
