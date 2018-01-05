from antlr4 import *
from BSVLexer import BSVLexer
from BSVListener import BSVListener
from BSVParser import BSVParser
import sys

class BSVPrintListener(BSVListener):
    def enterModuledef(self, ctx):
        print("BSV module: %s" % ctx.moduleproto().modulename.getText())

def main():
    for filename in sys.argv[1:]:
        print("parsing BSV file %s" % filename)
        with open(filename, 'r') as f:
            lexer = BSVLexer(InputStream(f.read()))
            stream = CommonTokenStream(lexer)
            parser = BSVParser(stream)
            tree = parser.packagedef()
            printer = BSVPrintListener()
            walker = ParseTreeWalker()
            walker.walk(printer, tree)

if __name__ == '__main__':
    main()
