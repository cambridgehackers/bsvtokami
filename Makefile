
all: gradlebuild kamibuild bin/bsv-parser-cpp

gradlebuild: z3/build/com.microsoft.z3.jar
	gradle build
	gradle installDist

z3/build/com.microsoft.z3.jar:
	git submodule update --init
	cd z3; ./configure --java; cd build; make -j4

bbv/Makefile:
	git submodule update --init

kamibuild: bbv/Makefile
	cd bbv; make
	cd coq-record-update; make
	cd kami; make
	cd kamilib; make
	cd tests/out; make
	cd example/out; make

installdist:
	gradle installDist

JARS = jars/antlr-4.7.1-complete.jar

test: connectal $(JARS) installdist
	./bsvparse tests/*.bsv
	./bsvparse connectal/bsv/*.bsv
	if [ -d ssith-riscv ]; then ./bsvparse ssith-riscv/procs/*/*.bsv ; fi
	make -C prooftests



generated/BSV.g4: src/main/antlr/bsvtokami/BSV.g4
	@mkdir -p generated
	sed 's/package bsvtokami;//' < src/main/antlr/bsvtokami/BSV.g4 > generated/BSV.g4

generated/BSVParser.java: generated/BSV.g4 $(JARS)
	java -jar $(JARS) -listener -visitor -o generated generated/BSV.g4

generated/BSVParser.cpp: generated/BSV.g4 $(JARS)
	java -jar $(JARS)  -Dlanguage=Cpp -listener -visitor generated/BSV.g4

python/BSVParser.py: src/main/antlr/bsvtokami/BSV.g4 $(JARS)
	pip3 install -q -r requirements.txt
	java -jar $(JARS)  -Dlanguage=Python3 -listener -visitor -o python src/main/antlr/bsvtokami/BSV.g4

GENERATED_SRCS = $(wildcard generated/*.cpp)
GENERATED_OBJS = $(patsubst %.cpp,%.o,$(GENERATED_SRCS))

generated/%.o: generated/%.cpp
	$(CXX) -c -O -Wno-attributes -Wno-unused-but-set-variable -Wall -std=c++11 -Igenerated -Iantlr4-cpp-runtime/runtime/src/ -o generated/$(*).o generated/$(*).cpp

generated/libBSVParser.a: generated/BSVParser.cpp $(GENERATED_OBJS)
	echo $(GENERATED_SRCS)
	@echo AR libBSVParser.a
	ar crs generated/libBSVParser.a $(GENERATED_OBJS)

bin/bsv-parser-cpp: cpp/main.cpp cpp/StaticAnalyzer.h generated/libBSVParser.a
	test -f /usr/include/z3.h || echo sudo apt install z3-dev
	mkdir -p bin
	$(CXX) -O -Wall -std=c++11 -Igenerated -Iantlr4-cpp-runtime/runtime/src/ -o bin/bsv-parser-cpp cpp/main.cpp -Lgenerated -lBSVParser antlr4-cpp-runtime/dist/libantlr4-runtime.a -lz3

antlr4-cpp-runtime: antlr4-cpp-runtime-4.7.1-source.zip
	rm -fr antlr4-cpp-runtime/*
	mkdir -p antlr4-cpp-runtime; cd antlr4-cpp-runtime; unzip ../antlr4-cpp-runtime-4.7.1-source.zip

antlr4-cpp-runtime/dist/libantlr4-runtime.a: antlr4-cpp-runtime
	pkg-config --version uuid || echo sudo apt install Install uuid-dev
	mkdir -p build-antlr4; cd build-antlr4; cmake ../antlr4-cpp-runtime; make -j4

antlr4-cpp-runtime-4.7.1-source.zip:
	curl -L https://www.antlr.org/download/antlr4-cpp-runtime-4.7.1-source.zip > antlr4-cpp-runtime-4.7.1-source.zip

$(JARS):
	mkdir -p jars
	curl -L https://www.antlr.org/download/antlr-4.7.1-complete.jar > jars/antlr-4.7.1-complete.jar

connectal:
	git clone --depth=1 git://github.com/cambridgehackers/connectal

clean:
	rm -fr build
	rm -fr classes bin
	make -C prooftests clean
