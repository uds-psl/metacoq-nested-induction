# with coq 8.11
all:
	cd metacoq && ./configure.sh local && make -j 4 && make install
	cd metacoq/translations && make -j 4 && make install
	cd source && make && make install

# with coq 8.9
typing:
	cd metacoq_8_9 && ./configure.sh local && make -j 4
	cd source_typing && make

# vim:ft=make
#
