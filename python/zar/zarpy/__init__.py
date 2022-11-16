"""
Discrete uniform sampler Ocaml library exposed to Python
"""

import os
from ctypes import PyDLL, RTLD_GLOBAL, c_char_p

curdir = dir_path = os.path.dirname(os.path.realpath(__file__))
dll = PyDLL(f"{curdir}/zarpy.so", RTLD_GLOBAL)
argv_t = c_char_p * 2
argv = argv_t("zarpy.so".encode('utf-8'), None)
dll.caml_startup(argv)

# We export the names explicitly otherwise mypy gets confused and
# generates spurious errors
from zarpy import seed, build, single, many, many_entropy
