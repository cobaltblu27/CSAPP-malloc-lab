cmake_minimum_required(VERSION 3.9)
project(malloclab_handout)

set(CMAKE_CXX_STANDARD 11)

add_executable(malloclab_handout
        clock.c
        clock.h
        config.h
        fcyc.c
        fcyc.h
        fsecs.c
        fsecs.h
        ftimer.c
        ftimer.h
        mdriver.c
        memlib.c
        memlib.h
        mm.c
        mm.h)
