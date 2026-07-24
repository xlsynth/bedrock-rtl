# SPDX-License-Identifier: Apache-2.0

FROM docker.io/library/rockylinux:8.9.20231119@sha256:2d05a9266523bbf24f33ebc3a9832e4d5fd74b973c220f2204ca802286aa275d
ARG TARGETPLATFORM
WORKDIR /tmp
COPY requirements_lock_3_12.txt /tmp/requirements_lock_3_12.txt
COPY scripts/requirements.txt /tmp/scripts_requirements.txt

RUN if [ "${TARGETPLATFORM}" != "linux/amd64" ]; then \
        echo "This Dockerfile does not yet support non-amd64 platforms because Bazel hasn't provided Docker images for them yet."; \
        echo "Your platform might be able to emulate other platforms, though. Try building the image with --platform linux/amd64."; \
        exit 1; \
    fi

# Install build-time dependencies and other helpful yum packages. Rocky Linux 8
# only packages CMake 3.26, but the pinned slang submodule requires CMake 3.28
# or newer, so install a pinned Kitware build in the same layer.
RUN yum install -y dnf-plugins-core-4.0.21-25.el8 && \
    yum config-manager --set-enabled \
        plus \
        powertools && \
    yum install -y \
        autoconf-2.69-29.el8_10.1 \
        bison-3.0.4-10.el8 \
        boost-1.66.0-13.el8 \
        boost-python3-devel-1.66.0-13.el8 \
        boost-system-1.66.0-13.el8 \
        clang-18.1.8-1.module+el8.10.0+1875+4f0b06db \
        curl-7.61.1-34.el8_10.3 \
        eigen3-devel-3.3.4-6.el8 \
        emacs-26.1-13.el8_10 \
        flex-2.6.1-9.el8 \
        gawk-4.2.1-4.el8 \
        gcc-8.5.0-23.el8_10 \
        gcc-c++-8.5.0-23.el8_10 \
        git-2.43.5-2.el8_10 \
        glibc-2.28-251.el8_10.13 \
        glibc-devel-2.28-251.el8_10.13 \
        gmp-6.1.2-12.el8 \
        gmp-devel-1:6.1.2-12.el8 \
        gperf-3.1-5.el8 \
        graphviz-2.40.1-45.el8 \
        help2man-1.47.6-1.el8 \
        jq-1.6-12.el8_10 \
        libatomic-8.5.0-23.el8_10 \
        libffi-3.1-24.el8 \
        libffi-devel-3.1-24.el8.x86_64 \
        libnsl-2.28-251.el8_10.13 \
        libstdc++-8.5.0-23.el8_10 \
        libstdc++-devel-8.5.0-23.el8_10 \
        lld-18.1.8-1.module+el8.10.0+1875+4f0b06db \
        make-4.2.1-11.el8 \
        numactl-2.0.16-4.el8 \
        perl-5.26.3-422.el8 \
        pkgconf-pkg-config-1.4.2-1.el8 \
        python3.12-3.12.8-1.el8_10 \
        python3.12-pip-23.2.1-4.el8 \
        readline-7.0-10.el8 \
        readline-devel-7.0-10.el8 \
        swig-3.0.12-19.module+el8.4.0+385+82b6e804 \
        tcl-devel-1:8.6.8-2.el8 \
        vim-enhanced-2:8.0.1763-19.el8_6.4 \
        zlib-1.2.11-26.el8 \
        zlib-devel-1.2.11-26.el8 && \
    yum clean all && \
    rm -rf /var/cache/yum && \
    curl -L https://github.com/Kitware/CMake/releases/download/v3.31.6/cmake-3.31.6-linux-x86_64.sh -o cmake-3.31.6-linux-x86_64.sh && \
    echo "518c76bd18cc4ca5faab891db69b1289dc1bf134f394f0983a19576711b95210  cmake-3.31.6-linux-x86_64.sh" | sha256sum -c - && \
    sh cmake-3.31.6-linux-x86_64.sh --skip-license --prefix=/usr/local && \
    rm cmake-3.31.6-linux-x86_64.sh && \
    cmake --version

RUN pip3.12 install --require-hashes -r /tmp/requirements_lock_3_12.txt && \
    rm /tmp/requirements_lock_3_12.txt
RUN pip3.12 install -r /tmp/scripts_requirements.txt && \
    rm /tmp/scripts_requirements.txt

# Install Verilator
# v5.050 - devel
RUN git clone https://github.com/verilator/verilator && \
    cd verilator && \
    git checkout 796d5174f385125958e64a3f49e1257fc8fc4222 && \
    autoconf && \
    CC="clang -fuse-ld=lld" CXX="clang++ -fuse-ld=lld" ./configure && \
    make -j$(nproc) && \
    make install && \
    cd .. && \
    rm -rf verilator && \
    verilator --version

# Install Verible
RUN curl -L https://github.com/chipsalliance/verible/releases/download/v0.0-4023-gc1271a00/verible-v0.0-4023-gc1271a00-linux-static-x86_64.tar.gz -o verible-v0.0-4023-gc1271a00-linux-static-x86_64.tar.gz && \
    echo "30c20385956f52ef892cb58f7f816f9f9a9dc37a0432848a49c6d9aa3a72a8b7  verible-v0.0-4023-gc1271a00-linux-static-x86_64.tar.gz" | sha256sum -c - && \
    tar -xzf verible-v0.0-4023-gc1271a00-linux-static-x86_64.tar.gz && \
    cp verible-v0.0-4023-gc1271a00/bin/* /usr/local/bin/ && \
    verible-verilog-lint --version && \
    rm verible-v0.0-4023-gc1271a00-linux-static-x86_64.tar.gz && \
    rm -rf verible-v0.0-4023-gc1271a00

# Yosys 0.65 requires Bison 3.6 or newer; Rocky Linux 8 packages Bison 3.0.
RUN curl -L https://ftp.gnu.org/gnu/bison/bison-3.8.2.tar.gz -o bison-3.8.2.tar.gz && \
    echo "06c9e13bdf7eb24d4ceb6b59205a4f67c2c7e7213119644430fe82fbd14a0abb  bison-3.8.2.tar.gz" | sha256sum -c - && \
    tar -xzf bison-3.8.2.tar.gz && \
    cd bison-3.8.2 && \
    ./configure && \
    make -j$(nproc) && \
    make install && \
    cd .. && \
    rm -rf bison-3.8.2 bison-3.8.2.tar.gz && \
    bison --version

# Install Yosys
# v0.66
RUN git clone https://github.com/YosysHQ/yosys.git && \
    cd yosys && \
    git fetch --all && \
    git checkout 86f2ddebce7e98ce7cacc27e8a5c14cb53b51b51 && \
    git submodule update --init --recursive && \
    make config-clang && \
    make -j$(nproc) && \
    make install && \
    cd .. && \
    rm -rf yosys && \
    yosys --help

# The pinned slang submodule requires Boost.Unordered headers newer than the
# Boost 1.66 headers shipped by Rocky Linux 8.
RUN curl -L https://archives.boost.io/release/1.88.0/source/boost_1_88_0.tar.gz -o boost_1_88_0.tar.gz && \
    echo "3621533e820dcab1e8012afd583c0c73cf0f77694952b81352bf38c1488f9cb4  boost_1_88_0.tar.gz" | sha256sum -c - && \
    tar -xzf boost_1_88_0.tar.gz && \
    cp -R boost_1_88_0/boost /usr/local/include/ && \
    rm -rf boost_1_88_0 boost_1_88_0.tar.gz

# Install the Slang SystemVerilog frontend plugin for Yosys.
# yosys-slang does not publish release tags. This is the first upstream
# commit that declares support for Yosys 0.66.
RUN git clone https://github.com/povik/yosys-slang.git && \
    cd yosys-slang && \
    git checkout 23193003ee2c2297ec8b6cbc8f6f9cdb0e732a47 && \
    git submodule update --init --recursive && \
    CC=clang CXX=clang++ make -j$(nproc) && \
    cmake --install build && \
    cd .. && \
    rm -rf yosys-slang && \
    yosys -m slang -p "help read_slang"

# Install EQY
# v0.48
RUN git clone https://github.com/YosysHQ/eqy.git && \
    cd eqy && \
    git checkout 93bf4dfb8b19c0f1e9d472fd8421cdfdc4fe85a0 && \
    make -j$(nproc) && \
    make install && \
    cd .. && \
    rm -rf eqy && \
    eqy --help

# Yices-2.6.5
RUN git clone https://github.com/SRI-CSL/yices2.git && \
    cd yices2 && \
    git checkout 8e6297e233299631147f98659224c3118fc6a215 && \
    autoconf && \
    ./configure && \
    make -j$(nproc) && \
    make install && \
    cd .. && \
    rm -rf yices2 && \
    yices --version

# Install Slang. Make sure to tell it to use clang,
# because our gcc install in this image is too old for C++20 language features.
# v7.0
RUN git clone https://github.com/MikePopoloski/slang.git && \
    cd slang && \
    git checkout d56a39898b24208871ac936cd535f9daacef36a7 && \
    CC=clang CXX=clang++ cmake -B build && \
    cmake --build build -j$(nproc) && \
    cp build/bin/slang /usr/local/bin/slang && \
    cd .. && \
    rm -rf slang && \
    slang -version

# Use Bazelisk to manage Bazel versions.
# This makes it easier to upgrade by changing .bazelversion in the Bedrock-RTL repo.
RUN curl -L https://github.com/bazelbuild/bazelisk/releases/download/v1.27.0/bazelisk-linux-amd64 -o /usr/local/bin/bazelisk && \
    echo "e1508323f347ad1465a887bc5d2bfb91cffc232d11e8e997b623227c6b32fb76  /usr/local/bin/bazelisk" | sha256sum -c - && \
    mv /usr/local/bin/bazelisk /usr/local/bin/bazel && \
    chmod +x /usr/local/bin/bazel

# Clone z3 to use as a verilator solver
# z3-4.16.0
RUN git clone https://github.com/Z3Prover/z3.git && \
    cd z3 && \
    git checkout ddb49568d3520e99799e364fb22f35fc67d887b1 && \
    CXX=clang++ CC=clang python3 ./scripts/mk_make.py && \
    cd build && make -j$(nproc) && make install && \
    cd ../.. && \
    rm -rf z3 && \
    z3 --version
# Export VERILATOR_SOLVER environmental variable to use z3 as a solver
ENV VERILATOR_SOLVER="z3 --in"

RUN useradd -m user
USER user

WORKDIR /home/user
LABEL description="Docker image for building and testing Bedrock-RTL using open source tools." \
    org.opencontainers.image.title="bedrock-rtl-dev" \
    org.opencontainers.image.description="Bedrock-RTL development image with an open source toolchain for building and testing." \
    org.opencontainers.image.source="https://github.com/xlsynth/bedrock-rtl" \
    org.opencontainers.image.licenses="Apache-2.0"
CMD ["/bin/bash"]
