#!/bin/sh

# This script installs the Nix package manager on your system by
# downloading a binary distribution and running its installer script
# (which in turn creates and populates /nix).

{ # Prevent execution if this script was only partially downloaded
oops() {
    echo "$0:" "$@" >&2
    exit 1
}

umask 0022

tmpDir="$(mktemp -d -t nix-binary-tarball-unpack.XXXXXXXXXX || \
          oops "Can't create temporary directory for downloading the Nix binary tarball")"
cleanup() {
    rm -rf "$tmpDir"
}
trap cleanup EXIT INT QUIT TERM

require_util() {
    command -v "$1" > /dev/null 2>&1 ||
        oops "you do not have '$1' installed, which I need to $2"
}

case "$(uname -s).$(uname -m)" in
    Linux.x86_64)
        hash=ff66236d2f7e2a21f3350e73668e021ac6a8881ef277a38e16e952bfb22718c3
        path=c7saa824rxx2288vjmgycz72pv94qycn/nix-2.35.4-x86_64-linux.tar.xz
        system=x86_64-linux
        ;;
    Linux.i?86)
        hash=f341f07ea223508238c57ae3dda585124744ba1b09422e29d32f068a8f2f439f
        path=107vfsbh246100h3wbsh9qc57bam4zr5/nix-2.35.4-i686-linux.tar.xz
        system=i686-linux
        ;;
    Linux.aarch64)
        hash=14a940a2d0ae5b2c623dc2ca168311c9367fd4bc416f6ded0c1087089d6de934
        path=rpmfbhcv3a8yi52z36xzwbw8s8rqk1ln/nix-2.35.4-aarch64-linux.tar.xz
        system=aarch64-linux
        ;;
    Linux.armv6l)
        hash=76744836ea6eae52810ee196126fc42214a224a4d2f0dc3e64dfcafe4695e820
        path=ws79a1x37is6nawnzpl9lc9y5xcdrshk/nix-2.35.4-armv6l-linux.tar.xz
        system=armv6l-linux
        ;;
    Linux.armv7l)
        hash=8029f7e67ad177093f58d19a80c55d8db8c697164da370bca2a5ed4124c41e81
        path=wkrw4hhkc7dxdq294a6x8r7qdvybfv4a/nix-2.35.4-armv7l-linux.tar.xz
        system=armv7l-linux
        ;;
    Linux.riscv64)
        hash=38edf052a1f9251f55e80d67b7611973684e72d2029d0d525c80ed7e62c6e1c4
        path=vsk3v7a4bd2d6yn2504cci44qyqhvfz6/nix-2.35.4-riscv64-linux.tar.xz
        system=riscv64-linux
        ;;
    Darwin.x86_64)
        hash=6453d85b33b1e6b45bd2c0f48d63d6bc163670190acefe0a8bc98f5c5ac33081
        path=wlj4gsg5hh9qyh0div895d10j79n6a25/nix-2.35.4-x86_64-darwin.tar.xz
        system=x86_64-darwin
        ;;
    Darwin.arm64|Darwin.aarch64)
        hash=ed0c6b25cc15e29c6cbc78d4c20a8e7add3f5f60fdf7b95dd5e99d74e9ba4e45
        path=mkyysddcpsbpdyxrc9yk1qhqhvywrj8x/nix-2.35.4-aarch64-darwin.tar.xz
        system=aarch64-darwin
        ;;
    FreeBSD.amd64|FreeBSD.x86_64)
        hash=36be131d5451b844b24f74f717a02a78bda720962539a3fbd32b1d0ad77db401
        path=3h4kprba9d1dd5hwq8lvj1gq5yk29l4f/nix-2.35.4-x86_64-freebsd.tar.xz
        system=x86_64-freebsd
        ;;
    *) oops "sorry, there is no binary distribution of Nix for your platform";;
esac

# Use this command-line option to fetch the tarballs using nar-serve or Cachix
if [ "${1:-}" = "--tarball-url-prefix" ]; then
    if [ -z "${2:-}" ]; then
        oops "missing argument for --tarball-url-prefix"
    fi
    url=${2}/${path}
    shift 2
else
    url=https://releases.nixos.org/nix/nix-2.35.4/nix-2.35.4-$system.tar.xz
fi

tarball=$tmpDir/nix-2.35.4-$system.tar.xz

require_util tar "unpack the binary tarball"
if [ "$(uname -s)" != "Darwin" ]; then
    require_util xz "unpack the binary tarball"
fi

if command -v curl > /dev/null 2>&1; then
    fetch() { curl --fail -L "$1" -o "$2"; }
elif command -v wget > /dev/null 2>&1; then
    fetch() { wget "$1" -O "$2"; }
else
    oops "you don't have wget or curl installed, which I need to download the binary tarball"
fi

echo "downloading Nix 2.35.4 binary tarball for $system from '$url' to '$tmpDir'..."
fetch "$url" "$tarball" || oops "failed to download '$url'"

if command -v sha256sum > /dev/null 2>&1; then
    hash2="$(sha256sum -b "$tarball" | cut -c1-64)"
elif command -v shasum > /dev/null 2>&1; then
    hash2="$(shasum -a 256 -b "$tarball" | cut -c1-64)"
elif command -v openssl > /dev/null 2>&1; then
    hash2="$(openssl dgst -r -sha256 "$tarball" | cut -c1-64)"
else
    oops "cannot verify the SHA-256 hash of '$url'; you need one of 'shasum', 'sha256sum', or 'openssl'"
fi

if [ "$hash" != "$hash2" ]; then
    oops "SHA-256 hash mismatch in '$url'; expected $hash, got $hash2"
fi

unpack=$tmpDir/unpack
mkdir -p "$unpack"
tar -xJf "$tarball" -C "$unpack" || oops "failed to unpack '$url'"

script=$(echo "$unpack"/*/install)

[ -e "$script" ] || oops "installation script is missing from the binary tarball!"
export INVOKED_FROM_INSTALL_IN=1
"$script" "$@"

} # End of wrapping
