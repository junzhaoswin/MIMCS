cmake_minimum_required(VERSION 3.16)
project(MIMCS LANGUAGES CXX)

add_executable(mimcs src/mimc_lift.cpp)
target_compile_features(mimcs PRIVATE cxx_std_17)
target_compile_options(mimcs PRIVATE
    $<$<CXX_COMPILER_ID:GNU,Clang,AppleClang>:-O3;-Wall;-Wextra>
)
