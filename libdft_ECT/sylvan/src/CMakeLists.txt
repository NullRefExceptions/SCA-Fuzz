target_sources(Sylvan 
  PRIVATE
    lace.cpp
    sha2.c
    sylvan_bdd.c
    sylvan_cache.c
    sylvan_common.c
    sylvan_hash.c
    sylvan_ldd.c
    sylvan_mt.c
    sylvan_mtbdd.c
    sylvan_refs.c
    sylvan_sl.c
    sylvan_stats.c
    sylvan_table.c
  PUBLIC
    $<INSTALL_INTERFACE:include/lace.h>
    $<INSTALL_INTERFACE:include/sylvan.h>
    $<INSTALL_INTERFACE:include/sylvan_bdd.h>
    $<INSTALL_INTERFACE:include/sylvan_cache.h>
    $<INSTALL_INTERFACE:include/sylvan_config.h>
    $<INSTALL_INTERFACE:include/sylvan_common.h>
    $<INSTALL_INTERFACE:include/sylvan_hash.h>
    $<INSTALL_INTERFACE:include/sylvan_int.h>
    $<INSTALL_INTERFACE:include/sylvan_ldd.h>
    $<INSTALL_INTERFACE:include/sylvan_ldd_int.h>
    $<INSTALL_INTERFACE:include/sylvan_mt.h>
    $<INSTALL_INTERFACE:include/sylvan_mtbdd.h>
    $<INSTALL_INTERFACE:include/sylvan_mtbdd_int.h>
    $<INSTALL_INTERFACE:include/sylvan_stats.h>
    $<INSTALL_INTERFACE:include/sylvan_table.h>
    $<INSTALL_INTERFACE:include/sylvan_tls.h>
    $<BUILD_INTERFACE:${CMAKE_CURRENT_LIST_DIR}/lace.h>
    $<BUILD_INTERFACE:${CMAKE_CURRENT_LIST_DIR}/sylvan.h>
    $<BUILD_INTERFACE:${CMAKE_CURRENT_LIST_DIR}/sylvan_bdd.h>
    $<BUILD_INTERFACE:${CMAKE_CURRENT_LIST_DIR}/sylvan_cache.h>
    $<BUILD_INTERFACE:${CMAKE_CURRENT_LIST_DIR}/sylvan_config.h>
    $<BUILD_INTERFACE:${CMAKE_CURRENT_LIST_DIR}/sylvan_common.h>
    $<BUILD_INTERFACE:${CMAKE_CURRENT_LIST_DIR}/sylvan_hash.h>
    $<BUILD_INTERFACE:${CMAKE_CURRENT_LIST_DIR}/sylvan_int.h>
    $<BUILD_INTERFACE:${CMAKE_CURRENT_LIST_DIR}/sylvan_ldd.h>
    $<BUILD_INTERFACE:${CMAKE_CURRENT_LIST_DIR}/sylvan_ldd_int.h>
    $<BUILD_INTERFACE:${CMAKE_CURRENT_LIST_DIR}/sylvan_mt.h>
    $<BUILD_INTERFACE:${CMAKE_CURRENT_LIST_DIR}/sylvan_mtbdd.h>
    $<BUILD_INTERFACE:${CMAKE_CURRENT_LIST_DIR}/sylvan_mtbdd_int.h>
    $<BUILD_INTERFACE:${CMAKE_CURRENT_LIST_DIR}/sylvan_stats.h>
    $<BUILD_INTERFACE:${CMAKE_CURRENT_LIST_DIR}/sylvan_table.h>
    $<BUILD_INTERFACE:${CMAKE_CURRENT_LIST_DIR}/sylvan_tls.h>
)

set(PIN_DEFINE -D__PIN__=1 -DPIN_CRT=1 -DNO_PINTOOL_LOG -DTARGET_IA32E -DHOST_IA32E  -DTARGET_LINUX -DBYTE_ORDER=LITTLE_ENDIAN)
set(PIN_CFLAG -march=native -mfsgsbase -Wno-unknown-pragmas -Wno-unused-parameter -fPIC -fabi-version=2 -funwind-tables -fno-stack-protector -fasynchronous-unwind-tables -fomit-frame-pointer -fno-strict-aliasing)
set(PIN_LINK_FLAG -L/root/pin-3.26/intel64/runtime/pincrt -nostdlib )
set(PIN_LIB c-dynamic m-dynamic c++ c++abi)
set(PIN_INCLUDE 
    /root/pin-3.26/source/include/pin
    /root/pin-3.26/source/include/pin/gen

    /root/pin-3.26/extras/cxx/include
    /root/pin-3.26/extras/crt/include 
    /root/pin-3.26/extras/crt/include/arch-x86_64 
    /root/pin-3.26/extras/crt/include/kernel/uapi 
    /root/pin-3.26/extras/crt/include/kernel/uapi/asm-x86
    /root/pin-3.26/extras/components/include 
    /root/pin-3.26/extras/xed-intel64/include/xed)

target_compile_features(Sylvan PUBLIC c_std_11 cxx_std_11)
target_compile_options(Sylvan PRIVATE -Wall -Wextra -fno-strict-aliasing -Wno-deprecated ${PIN_DEFINE} ${PIN_CFLAG})

target_include_directories(Sylvan
  PUBLIC
    $<BUILD_INTERFACE:${CMAKE_CURRENT_LIST_DIR}>
    $<INSTALL_INTERFACE:include>
    ${PIN_INCLUDE}
    
)
target_link_libraries(Sylvan PUBLIC ${PIN_LIB} )
target_link_options(Sylvan PUBLIC ${PIN_LINK_FLAG})

# Do we want to collect BDD statistics?
option(SYLVAN_STATS "Collect statistics" OFF)
if(SYLVAN_STATS)
  set_target_properties(Sylvan PROPERTIES COMPILE_DEFINITIONS "SYLVAN_STATS")
endif()

option(SSA_NOGC "NOGC" OFF)
if(SSA_NOGC)
  set_target_properties(Sylvan PROPERTIES COMPILE_DEFINITIONS "SSA_NOGC")
endif()

option(SSA_PROFILE "PROFILE" OFF)
if(SSA_PROFILE)
  set_target_properties(Sylvan PROPERTIES COMPILE_DEFINITIONS "SSA_PROFILE")
endif()

get_target_property(Sylvan_PUBLIC_HEADERS Sylvan INTERFACE_SOURCES)
set_target_properties(Sylvan PROPERTIES PUBLIC_HEADER "${Sylvan_PUBLIC_HEADERS}")
