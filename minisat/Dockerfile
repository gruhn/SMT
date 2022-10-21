FROM buildpack-deps

WORKDIR /
RUN git clone https://github.com/niklasso/minisat.git
WORKDIR /minisat
RUN make config prefix=$PREFIX
RUN make install