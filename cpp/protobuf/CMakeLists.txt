find_package(Protobuf REQUIRED)
include_directories(${Protobuf_INCLUDE_DIRS})
include_directories(${CMAKE_CURRENT_BINARY_DIR})
set(CMAKE_CXX_FLAGS "-O -g -std=c++14")

protobuf_generate_cpp(PROTO_SRCS PROTO_HDRS foo.proto)
protobuf_generate_cpp(PROTO_SRCS PROTO_HDRS
        bsvtype.proto
        source_pos.proto
        expr.proto
        lvalue.proto
        pattern.proto
        stmt.proto)
protobuf_generate_python(PROTO_PY
        bsvtype.proto
        source_pos.proto
        expr.proto
        lvalue.proto
        pattern.proto
        stmt.proto)
add_library(bsvproto ${PROTO_SRCS} ${PROTO_HDRS})
target_link_libraries(bsvproto ${Protobuf_LIBRARIES})
message("PROTO_PY ${PROTO_PY}")
add_custom_target(bsvprotopy ALL
        DEPENDS ${PROTO_PY})