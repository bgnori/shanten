FROM mcr.microsoft.com/devcontainers/go:1-1.24-bookworm

ENV ELAN_HOME=/usr/local/elan
ENV PATH="/usr/local/elan/bin:${PATH}"

RUN rm -f /etc/apt/sources.list.d/yarn.list \
    && apt-get update \
    && apt-get install -y --no-install-recommends ca-certificates curl \
    && curl --proto '=https' --tlsv1.2 -sSf https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -o /tmp/elan-init.sh \
    && sh /tmp/elan-init.sh -y --no-modify-path --default-toolchain none \
    && rm /tmp/elan-init.sh \
    && ln -s "${ELAN_HOME}/bin/"* /usr/local/bin/ \
    && chown -R vscode:vscode "${ELAN_HOME}" \
    && apt-get clean \
    && rm -rf /var/lib/apt/lists/*
