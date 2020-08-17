#!/usr/bin/env python3

import argparse
import os
import sys

sys.path.insert(0, os.path.join(os.path.dirname(os.path.dirname(os.path.abspath(__name__))), 'cpp', 'build', 'protobuf'))

import bsvtype_pb2
import expr_pb2
import pattern_pb2
import source_pos_pb2
import stmt_pb2

def parse_packagedef(filename):
    with open(filename, 'rb') as f:
        packagedef_bytes = f.read()
        packagedef = stmt_pb2.PackageDef()
        packagedef.ParseFromString(packagedef_bytes)
        return packagedef


argparser = argparse.ArgumentParser('read bsvtokami AST files')
argparser.add_argument('ast_files', help='AST files', action='append')

if __name__ == '__main__':
    args = argparser.parse_args()
    ast_files = args.ast_files
    for ast_file in ast_files:
        print(ast_file)
        packagedef = parse_packagedef(ast_file)
        print(packagedef)
