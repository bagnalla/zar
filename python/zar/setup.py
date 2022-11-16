from distutils.core import setup

NAME = "zarpy"

setup(
    name=NAME,
    version="0.9.1",
    author="Alexander Bagnall",
    author_email="abagnalla@gmail.com",
    description="Formally verified-correct n-sided die roller",
    long_description=open('README.md', 'r').read(),
    long_description_content_type='text/markdown',
    packages=[NAME],
    package_data={NAME: ['zarpy.so']})
