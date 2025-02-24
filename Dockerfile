# TODO: This Dockerfile is not yet usable for building and testing Bedrock-RTL. WIP.

FROM ubuntu:24.04
ARG TARGETPLATFORM
LABEL description="Docker image for building and testing Bedrock-RTL"
WORKDIR /work

RUN if [ "${TARGETPLATFORM}" != "linux/amd64" ]; then \
        echo "This Dockerfile does not yet support non-amd64 platforms because Bazel hasn't provided Docker images for them yet."; \
        echo "Your platform might be able to emulate other platforms, though. Try building the image with --platform linux/amd64."; \
        exit 1; \
    fi

# Install build-time dependencies
RUN apt update
RUN apt install -y bison=2:3.8.2+dfsg-1+b1
RUN apt install -y build-essential=12.9
RUN apt install -y clang=1:14.0-55.7~deb12u1
RUN apt install -y flex=2.6.4-8.2
RUN apt install -y gawk=1:5.2.1-2
RUN apt install -y git=1:2.39.5-0+deb12u2
RUN apt install -y gperf=3.1-1
RUN apt install -y graphviz=2.42.2-7+deb12u1
RUN apt install -y libboost-filesystem-dev=1.74.0.3
RUN apt install -y libboost-python-dev=1.74.0.3
RUN apt install -y libboost-system-dev=1.74.0.3
RUN apt install -y libffi-dev=3.4.4-1
RUN apt install -y libreadline-dev=8.2-1.3
RUN apt install -y lld=1:14.0-55.7~deb12u1
RUN apt install -y pkg-config=1.8.1-1
RUN apt install -y python3=3.11.2-1+b1
RUN apt install -y tcl-dev=8.6.13
RUN apt install -y xdot=1.2-3
RUN apt install -y zlib1g-dev=1:1.2.13.dfsg-1

# Install iverilog
RUN git clone https://github.com/steveicarus/iverilog.git && \
    cd iverilog && \
    git checkout v12-branch && \
    sh autoconf.sh && \
    ./configure && \
    make -j$(nproc) && \
    make install && \
    cd .. && \
    rm -rf iverilog
RUN iverilog -V

# Install Verible
RUN curl -L https://github.com/chipsalliance/verible/releases/download/v0.0-3946-g851d3ff4/verible-v0.0-3946-g851d3ff4-linux-static-x86_64.tar.gz && \
    tar -xzf verible-v0.0-3946-g851d3ff4-linux-static-x86_64.tar.gz && \
    cp verible-v0.0-3946-g851d3ff4-linux-static-x86_64/bin/* /usr/local/bin/ && \
    verible-verilog-lint --version && \
    rm verible-v0.0-3946-g851d3ff4-linux-static-x86_64.tar.gz && \
    rm -rf verible-v0.0-3946-g851d3ff4-linux-static-x86_64

# Install Yosys
RUN git clone --recurse-submodules https://github.com/YosysHQ/yosys.git && \
    cd yosys && \
    git checkout v0.48 && \
    make -j$(nproc) && \
    make install && \
    cd .. && \
    rm -rf yosys
RUN yosys --help

# Install EQY
RUN git clone https://github.com/YosysHQ/eqy.git eqy && \
    cd eqy && \
    git checkout v0.48 && \
    make -j$(nproc) && \
    make install && \
    cd .. && \
    rm -rf eqy
RUN eqy --help

# Install SBY
RUN git clone https://github.com/YosysHQ/sby && \
    cd sby && \
    git checkout v0.48 && \
    make -j$(nproc) && \
    make install && \
    cd .. && \
    rm -rf sby
RUN sby --help

# Install Bazel
# The Bazel image is implicitly linux/amd64: https://github.com/bazelbuild/continuous-integration/issues/2020
COPY --from=gcr.io/bazel-public/bazel:7.3.1 /usr/local/bin/bazel /usr/local/bin/bazel
RUN bazel --version

RUN useradd -m user
USER user

CMD ["/bin/bash"]
