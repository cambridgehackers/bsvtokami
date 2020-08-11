
cmake_minimum_required(VERSION 3.0)
project(bsv-parser)

link_directories(
        antlr4-cpp-runtime/dist
        ../z3/build
)
add_subdirectory(protobuf)

set(SOURCE
        BSVType.cpp
        Expr.cpp
        Stmt.cpp
        GenerateAst.cpp
        GenerateIR.cpp
        Inliner.cpp
        LexicalScope.cpp
        TypeChecker.cpp
        main.cpp
        generated/BSVBaseListener.cpp
        generated/BSVBaseVisitor.cpp
        generated/BSVLexer.cpp
        generated/BSVListener.cpp
        generated/BSVParser.cpp
        generated/BSVVisitor.cpp
        GenerateIR.cpp GenerateIR.h
        BSVPreprocessor.cpp BSVPreprocessor.h
        GenerateKami.cpp GenerateKami.h
        LValue.cpp LValue.h
        GenerateKoika.cpp GenerateKoika.h
        Pattern.cpp Pattern.h
        SimplifyAst.cpp SimplifyAst.h
        Declaration.cpp
        SourcePos.h
        AttributeInstanceVisitor.cpp
        AttributeInstanceVisitor.h
        TopologicalSort.cpp TopologicalSort.h
        AstVisitor.cpp AstVisitor.h
        AstWriter.cpp AstWriter.h)
set(CMAKE_CXX_FLAGS "-O -g -std=c++14")
add_executable(bsv-parser ${SOURCE})
target_include_directories(bsv-parser
        PRIVATE
        generated
        ${CMAKE_CURRENT_BINARY_DIR}/protobuf
        ../z3/src/api
        ../z3/src/api/c++
        antlr4-cpp-runtime/runtime/src
        /usr/local/include
        )
target_link_libraries(bsv-parser
        bsvproto
        antlr4-runtime
        z3
        )
