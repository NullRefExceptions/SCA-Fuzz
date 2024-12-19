all: exec_server libscamutator.so

exec_server: exec_server.c
	$(CC) $(CFLAGS) -O0 -g ./exec_server.c -lpthread -o exec_server

libscamutator.so: sca_mutator.cpp
	$(CXX) $(CXXFLAGS) -fpermissive -D_FORTIFY_SOURCE=2 -O0 -fPIC -shared -g -I ../../include sca_mutator.cpp ./afl-performance.o -lpthread -o libscamutator.so

clean:
	rm libscamutator.so exec_server
