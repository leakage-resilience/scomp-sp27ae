FROM docker.io/library/debian:trixie
RUN apt update \
    && apt upgrade -y \
    && apt install -y nix

WORKDIR /code
COPY . .

RUN nix --experimental-features "nix-command flakes" develop --command true

ENTRYPOINT ["nix", "--experimental-features", "nix-command flakes", "develop"]
