# TODO: This Dockerfile is not yet usable for building and testing Bedrock-RTL. WIP.

# iverilog build image (not yet used)
FROM ubuntu:24.04 AS stage_iverilog
WORKDIR /
RUN apt update
RUN apt install -y git
RUN apt install -y gperf
RUN apt install -y flex
RUN apt install -y bison
RUN apt install -y autoconf
RUN apt install -y make
RUN apt install -y g++
RUN git clone https://github.com/steveicarus/iverilog.git
WORKDIR /iverilog
RUN git switch v12-branch
RUN sh autoconf.sh
RUN ./configure
RUN make -j$(nproc)
RUN make install
RUN iverilog -V

# user image
FROM ubuntu:24.04 AS user
ARG TARGETPLATFORM
LABEL description="Docker image for building and testing Bedrock-RTL"
WORKDIR /
RUN apt update
# Our Bazel rule implementations depend on a python3 system interpreter
RUN apt install -y python3
# One of the Bazel dependencies expects to find a C compiler on the system path
RUN apt install -y gcc
COPY --from=stage_iverilog /usr/local/bin/iverilog /usr/local/bin/iverilog
RUN if [ "${TARGETPLATFORM}" != "linux/amd64" ]; then \
        echo "This Dockerfile does not yet support non-amd64 platforms because Bazel hasn't provided Docker images for them yet."; \
        echo "Your platform might be able to emulate other platforms, though. Try building the image with --platform linux/amd64."; \
        exit 1; \
    fi
# The Bazel image is implicitly linux/amd64: https://github.com/bazelbuild/continuous-integration/issues/2020
COPY --from=gcr.io/bazel-public/bazel:7.3.1 /usr/local/bin/bazel /usr/local/bin/bazel
RUN iverilog -V
RUN python3 --version
RUN bazel --version

RUN useradd -m user
USER user

CMD ["/bin/bash"]
