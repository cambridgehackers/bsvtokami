
all: gradlebuild

gradlebuild:
	gradle build

JARS = jars/antlr-4.7.1-complete.jar

test: connectal $(JARS)
	./bsvparse tests/*.bsv
	./bsvparse connectal/bsv/*.bsv
	if [ -d ssith-riscv ]; then ./bsvparse ssith-riscv/procs/*/*.bsv ; fi

generated/BSVParser.java: BSV.g4 $(JARS)
	java -jar $(JARS) -listener -visitor -o generated BSV.g4

generated/BSVParser.cpp: BSV.g4 $(JARS)
	java -jar $(JARS)  -Dlanguage=Cpp -listener -visitor -o generated BSV.g4

python/BSVParser.py: BSV.g4 $(JARS)
	pip3 install -q -r requirements.txt
	java -jar $(JARS)  -Dlanguage=Python3 -listener -visitor -o python BSV.g4

bin/bsv-parser-cpp: cpp/main.cpp cpp/BSVTypeVisitor.h generated/BSVParser.cpp antlr4-cpp-runtime/dist/libantlr4-runtime.a
	mkdir -p bin
	$(CXX) -O -Wall -std=c++11 -Igenerated -Iantlr4-cpp-runtime/runtime/src/ -o bin/bsv-parser-cpp cpp/main.cpp generated/*.cpp antlr4-cpp-runtime/dist/libantlr4-runtime.a

antlr4-cpp-runtime: antlr4-cpp-runtime-4.7.1-source.zip
	rm -fr antlr4-cpp-runtime/*
	mkdir -p antlr4-cpp-runtime; cd antlr4-cpp-runtime; unzip ../antlr4-cpp-runtime-4.7.1-source.zip

antlr4-cpp-runtime/dist/libantlr4-runtime.a: antlr4-cpp-runtime
	mkdir -p build-antlr4; cd build-antlr4; cmake ../antlr4-cpp-runtime; make -j4

antlr4-cpp-runtime-4.7.1-source.zip:
	curl http://www.antlr.org/download/antlr4-cpp-runtime-4.7.1-source.zip > antlr4-cpp-runtime-4.7.1-source.zip

$(JARS):
	mkdir -p jars
	curl http://www.antlr.org/download/antlr-4.7.1-complete.jar > jars/antlr-4.7.1-complete.jar

connectal:
	git clone --depth=1 git://github.com/cambridgehackers/connectal

clean:
	rm -fr classes bin
