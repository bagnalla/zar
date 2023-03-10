from distutils.core import setup

NAME = "zarpy"

setup(
    name=NAME,
    version="0.9.2",
    author="Alexander Bagnall",
    author_email="abagnalla@gmail.com",
    description="Formally verified biased coin and n-sided die",
    long_description=open('README.md', 'r').read(),
    long_description_content_type='text/markdown',
    packages=[NAME],
    package_data={NAME: ['zarpy.so']})
