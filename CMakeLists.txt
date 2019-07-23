
cmake_minimum_required(VERSION 3.0)
project(bsv-parser)
link_directories(
	antlr4-cpp-runtime/dist
	z3/build
	)

set (SOURCE
     cpp/BSVType.cpp
     cpp/Expr.cpp
     cpp/GenerateAst.cpp
     cpp/TypeChecker.cpp
     cpp/main.cpp
     generated/BSVBaseListener.cpp
     generated/BSVBaseVisitor.cpp
     generated/BSVLexer.cpp
     generated/BSVListener.cpp
     generated/BSVParser.cpp
     generated/BSVVisitor.cpp
     )
set(CMAKE_CXX_FLAGS "-O -g -std=c++14")
add_executable(${PROJECT_NAME} ${SOURCE})
target_include_directories(${PROJECT_NAME}
	PRIVATE
	generated
	z3/src/api
	z3/src/api/c++
	antlr4-cpp-runtime/runtime/src
	)
target_link_libraries(${PROJECT_NAME}
	antlr4-runtime
	z3
	)
