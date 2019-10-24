from setuptools import setup, Extension
import imp
import os.path

p = imp.find_module('numpy')[1]
include_dir = os.path.join(p,'core','include','numpy')
setup_dir = os.path.dirname(os.path.realpath(__file__))

ext = Extension('randSAT',['randSAT.cpp','RandGen.cpp','DummyOptions.cpp','core/Solver.cc','utils/System.cc'],
               include_dirs = [include_dir,setup_dir], extra_compile_args=['-std=c++11'],
               install_requires=['numpy'])

setup(name='randSAT', py_modules=['PyRandSAT'], ext_modules=[ext])
