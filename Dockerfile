# SPDX-License-Identifier: Apache-2.0

FROM rockylinux:8.9.20231119@sha256:2d05a9266523bbf24f33ebc3a9832e4d5fd74b973c220f2204ca802286aa275d
ARG TARGETPLATFORM
LABEL description="Docker image for building and testing Bedrock-RTL using open source tools."
WORKDIR /tmp
COPY requirements_lock_3_12.txt /tmp/requirements_lock_3_12.txt

RUN if [ "${TARGETPLATFORM}" != "linux/amd64" ]; then \
        echo "This Dockerfile does not yet support non-amd64 platforms because Bazel hasn't provided Docker images for them yet."; \
        echo "Your platform might be able to emulate other platforms, though. Try building the image with --platform linux/amd64."; \
        exit 1; \
    fi

# Install build-time dependencies and other helpful yum packages.
RUN yum install -y dnf-plugins-core-4.0.21-25.el8
RUN yum config-manager --set-enabled \
    appstream-debuginfo \
    appstream-source \
    baseos-debuginfo \
    baseos-source \
    plus \
    powertools \
    powertools-debuginfo \
    powertools-source

RUN yum install -y autoconf-2.69-29.el8_10.1
RUN yum install -y bison-3.0.4-10.el8
RUN yum install -y boost-1.66.0-13.el8
RUN yum install -y boost-python3-devel-1.66.0-13.el8
RUN yum install -y boost-system-1.66.0-13.el8
RUN yum install -y clang-18.1.8-1.module+el8.10.0+1875+4f0b06db
RUN yum install -y cmake-3.26.5-2.el8
RUN yum install -y curl-7.61.1-34.el8_10.3
RUN yum install -y eigen3-devel-3.3.4-6.el8
RUN yum install -y emacs-26.1-13.el8_10
RUN yum install -y flex-2.6.1-9.el8
RUN yum install -y gawk-4.2.1-4.el8
RUN yum install -y gcc-8.5.0-23.el8_10
RUN yum install -y gcc-c++-8.5.0-23.el8_10
RUN yum install -y git-2.43.5-2.el8_10
RUN yum install -y glibc-2.28-251.el8_10.13
RUN yum install -y glibc-devel-2.28-251.el8_10.13
RUN yum install -y gmp-6.1.2-12.el8
RUN yum install -y gmp-devel-1:6.1.2-12.el8
RUN yum install -y gperf-3.1-5.el8
RUN yum install -y graphviz-2.40.1-45.el8
RUN yum install -y help2man-1.47.6-1.el8
RUN yum install -y libffi-3.1-24.el8
RUN yum install -y libffi-devel-3.1-24.el8.x86_64
RUN yum install -y libnsl-2.28-251.el8_10.13
RUN yum install -y libstdc++-8.5.0-23.el8_10
RUN yum install -y libstdc++-devel-8.5.0-23.el8_10
RUN yum install -y lld-18.1.8-1.module+el8.10.0+1875+4f0b06db
RUN yum install -y make-4.2.1-11.el8
RUN yum install -y numactl-2.0.16-4.el8
RUN yum install -y perl-5.26.3-422.el8
RUN yum install -y pkgconf-pkg-config-1.4.2-1.el8
RUN yum install -y python3.12-3.12.8-1.el8_10
RUN yum install -y python3.12-pip-23.2.1-4.el8
RUN yum install -y readline-7.0-10.el8
RUN yum install -y readline-devel-7.0-10.el8
RUN yum install -y swig-3.0.12-19.module+el8.4.0+385+82b6e804
RUN yum install -y tcl-devel-1:8.6.8-2.el8
RUN yum install -y vim-enhanced-2:8.0.1763-19.el8_6.4
RUN yum install -y zlib-1.2.11-26.el8
RUN yum install -y zlib-devel-1.2.11-26.el8

RUN pip3.12 install --require-hashes -r /tmp/requirements_lock_3_12.txt

# Install iverilog
# git SHA from: Jan 3, 2025
RUN git clone https://github.com/steveicarus/iverilog.git
RUN cd iverilog && \
    git checkout 14375567c72b6f71cc93bec3b62cf43aaf34942e && \
    sh autoconf.sh && \
    ./configure && \
    make -j$(nproc) && \
    make install && \
    cd .. && \
    rm -rf iverilog
RUN iverilog -V

# Install Verilator
# v5.032
RUN git clone https://github.com/verilator/verilator
RUN cd verilator && \
    git checkout 8ff77e9d47351b0a59114929880687839a51840b && \
    autoconf && \
    ./configure && \
    make -j$(nproc) && \
    make install && \
    cd .. && \
    rm -rf verilator
RUN verilator --version

# Install Verible
RUN curl -L https://github.com/chipsalliance/verible/releases/download/v0.0-4023-gc1271a00/verible-v0.0-4023-gc1271a00-linux-static-x86_64.tar.gz -o verible-v0.0-4023-gc1271a00-linux-static-x86_64.tar.gz
RUN echo "30c20385956f52ef892cb58f7f816f9f9a9dc37a0432848a49c6d9aa3a72a8b7  verible-v0.0-4023-gc1271a00-linux-static-x86_64.tar.gz" | sha256sum -c -
RUN tar -xzf verible-v0.0-4023-gc1271a00-linux-static-x86_64.tar.gz && \
    cp verible-v0.0-4023-gc1271a00/bin/* /usr/local/bin/ && \
    verible-verilog-lint --version && \
    rm verible-v0.0-4023-gc1271a00-linux-static-x86_64.tar.gz && \
    rm -rf verible-v0.0-4023-gc1271a00

# Install Yosys
# v0.51
RUN git clone https://github.com/YosysHQ/yosys.git
RUN cd yosys && \
    git fetch --all && \
    git checkout c4b5190229616f7ebf8197f43990b4429de3e420 && \
    git submodule update --init --recursive && \
    make -j$(nproc) && \
    make install && \
    cd .. && \
    rm -rf yosys
RUN yosys --help

# Install EQY
# v0.48
RUN git clone https://github.com/YosysHQ/eqy.git
RUN cd eqy && \
    git checkout 93bf4dfb8b19c0f1e9d472fd8421cdfdc4fe85a0 && \
    make -j$(nproc) && \
    make install && \
    cd .. && \
    rm -rf eqy
RUN eqy --help

# Install SBY
# TODO: debug
#RUN git clone https://github.com/YosysHQ/sby
#RUN cd sby && \
#    # v0.48
#    git checkout 26b387466d224cd9e83a6f97d0b69d9dd59e56b5 && \
#    make -j$(nproc) && \
#    make install && \
#    cd .. && \
#    rm -rf sby
#RUN sby --help

# Install boolector and yices2 to able to run LEC with Yosys
# TODO: boolector is not able to build..
#RUN git clone https://github.com/boolector/boolector
#RUN cd boolector && \
#    # 3.2.4
#    git checkout 393cdfba3735d334bb4e6525500b8a0280dd41e6 && \
#    ./contrib/setup-lingeling.sh && \
#    ./contrib/setup-btor2tools.sh && \
#    ./configure.sh && \
#    cd build && \
#    make -j$(nproc) && \
#    cp build/bin/boolector /usr/local/bin/ && \
#    cp build/bin/btor* /usr/local/bin/ && \
#    cp deps/btor2tools/build/bin/btorsim /usr/local/bin/ && \
#    cd .. && \
#    rm -rf boolector
#RUN boolector --version

# Yices-2.6.5
RUN git clone https://github.com/SRI-CSL/yices2.git
RUN cd yices2 && \
    git checkout 8e6297e233299631147f98659224c3118fc6a215 && \
    autoconf && \
    ./configure && \
    make -j$(nproc) && \
    make install && \
    cd .. && \
    rm -rf yices2
RUN yices --version

# Necessary for building OpenSTA
RUN curl -L https://github.com/davidkebo/cudd/raw/c8d587ef3fbcc115977fed48a867aa6664ca11d0/cudd_versions/cudd-3.0.0.tar.gz -o cudd-3.0.0.tar.gz
RUN echo "b8e966b4562c96a03e7fbea239729587d7b395d53cadcc39a7203b49cf7eeb69  cudd-3.0.0.tar.gz" | sha256sum -c -
RUN tar -xzf cudd-3.0.0.tar.gz && \
    cd cudd-3.0.0 && \
    ./configure --prefix=/usr/local && \
    make -j$(nproc) && \
    make install && \
    cd .. && rm -rf cudd-3.0.0 && rm cudd-3.0.0.tar.gz

# Build eigen 3.4.0 manually because yum only gave us 3.3.4, too low for OpenSTA
#RUN curl -L https://gitlab.com/libeigen/eigen/-/archive/3.4.0/eigen-3.4.0.tar.gz -o eigen-3.4.0.tar.gz
#RUN echo "8586084f71f9bde545ee7fa6d00288b264a2b7ac3607b974e54d13e7162c1c72  eigen-3.4.0.tar.gz" | sha256sum -c -
#RUN tar -xzf eigen-3.4.0.tar.gz && \
#    cd eigen-3.4.0 && \
#    mkdir build && \
#    cd build && \
#    cmake .. && \
#    make -j$(nproc) && \
#    make install && \
#    cd ../.. && \
#    rm -rf eigen-3.4.0 && \
#    rm eigen-3.4.0.tar.gz

# TODO: not yet working because of missing eigen dependency
#RUN git clone https://github.com/The-OpenROAD-Project/OpenSTA.git
#RUN cd OpenSTA && \
#    git checkout 543361765b78269402dba2656c7fca19459a7b7f && \
#    mkdir build && \
#    cd build && \
#    cmake .. && \
#    make -j$(nproc) && \
#    make install && \
#    cd ../.. && \
#    rm -rf OpenSTA

# TODO: SKY130 PDK?

# Install Slang. Make sure to tell it to use clang,
# because our gcc install in this image is too old for C++20 language features.
# v7.0
RUN git clone https://github.com/MikePopoloski/slang.git
RUN cd slang && \
    git checkout d56a39898b24208871ac936cd535f9daacef36a7 && \
    CC=clang CXX=clang++ cmake -B build && \
    cmake --build build -j$(nproc) && \
    cp build/bin/slang /usr/local/bin/slang && \
    rm -rf slang
RUN slang -version

# Install XLS library.
#
# Needed by TopStitch, which is used during Bazel build of xlsynth/bedrock-rtl repo.
# Cannot directly depend on XLS through Bazel to prevent future circular dependencies (we plan for XLS to depend on bedrock-rtl).
RUN curl -L https://github.com/xlsynth/xlsynth/releases/download/v0.22.0/libxls-rocky8.so.gz -o /usr/local/lib/libxls-v0.22.0-rocky8.so.gz
RUN echo "e0ddd5d519ecafb402c427bb769cd42cef0b944bd6c6b4dcc5c7926566d735e7  /usr/local/lib/libxls-v0.22.0-rocky8.so.gz" | sha256sum -c -
RUN gunzip /usr/local/lib/libxls-v0.22.0-rocky8.so.gz

# Use Bazelisk to manage Bazel versions
# Makes it easier to upgrade by just changing .bazelversion file in the Bedrock-RTL repo.
RUN curl -L https://github.com/bazelbuild/bazelisk/releases/download/v1.25.0/bazelisk-linux-amd64 -o /usr/local/bin/bazelisk
RUN echo "fd8fdff418a1758887520fa42da7e6ae39aefc788cf5e7f7bb8db6934d279fc4  /usr/local/bin/bazelisk" | sha256sum -c -
RUN mv /usr/local/bin/bazelisk /usr/local/bin/bazel
RUN chmod +x /usr/local/bin/bazel
RUN bazel --version

RUN useradd -m user
USER user

WORKDIR /home/user
CMD ["/bin/bash"]
