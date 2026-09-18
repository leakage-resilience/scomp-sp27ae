cmake_minimum_required(VERSION 3.12)

set(CMAKE_C_STANDARD 11)
set(PICO_BOARD pico2)

include($ENV{PICO_SDK_PATH}/external/pico_sdk_import.cmake)

project(bench C CXX ASM)

pico_sdk_init()

if(DEFINED ENV{ORDER})
    set(LM_ORDER $ENV{ORDER})
else()
    set(LM_ORDER 1)
endif()
option(USE_JASMIN "Use Jasmin masked keccak (OFF = C implementation)" ON)

set(GADGETS_DIR  "${CMAKE_CURRENT_SOURCE_DIR}/..")
set(LIBMASKING_A "${GADGETS_DIR}/../_build/arm-m4/order${LM_ORDER}/libmasking.a")

add_library(libmasking STATIC IMPORTED)
set_target_properties(libmasking PROPERTIES IMPORTED_LOCATION "${LIBMASKING_A}")

add_executable(bench bench.c keccak-f.c random.c)

set_source_files_properties(keccak-f.c PROPERTIES COMPILE_FLAGS "-O0")

target_include_directories(bench PRIVATE "${GADGETS_DIR}")
target_compile_definitions(bench PRIVATE LM_ORDER=${LM_ORDER})
if(USE_JASMIN)
    target_compile_definitions(bench PRIVATE USE_JASMIN)
endif()
target_link_libraries(bench libmasking pico_stdlib)
target_link_options(bench PRIVATE -Wl,--no-warn-mismatch -Wl,-Map=output.map)

pico_enable_stdio_usb(bench 1)
pico_enable_stdio_uart(bench 0)
pico_add_extra_outputs(bench)
