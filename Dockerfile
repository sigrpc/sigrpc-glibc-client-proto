FROM debian:bookworm-slim AS builder

RUN apt-get update \
    && apt-get install -y --no-install-recommends \
        bison \
        gawk \
        gcc \
        g++ \
        make \
        python3 \
        rsync \
    && mkdir /glibc-build \
    && mkdir /opt/lib

COPY . /glibc

WORKDIR /glibc-build

RUN find /lib/$(uname -m)-linux-gnu/ -maxdepth 1 -type f,l,d  | xargs -I{} basename {} | xargs -I{} ln -s /lib/$(uname -m)-linux-gnu/{} /opt/lib/{} \
    && ../glibc/configure --prefix=/opt \
    && make -j $(nproc) \
    && make install

FROM debian:bookworm-slim

COPY --from=builder /opt/bin/ /opt/bin/
COPY --from=builder /opt/etc/ /opt/etc/
COPY --from=builder /opt/lib/ /opt/lib/
COPY --from=builder /opt/libexec/ /opt/libexec/
COPY --from=builder /opt/var/ /opt/var/

WORKDIR /
