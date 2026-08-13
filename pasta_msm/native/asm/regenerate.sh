#!/bin/sh
# Copyright Supranational LLC
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
# Modified by Zakura to regenerate every supported target deterministically.

set -eu

here=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
semolina="$here/../semolina"
perl_command=${PERL:-perl}

generate_file() {
    gf_source=$1
    gf_flavour=$2
    gf_destination=$3
    gf_comment=$4
    {
        printf '%s Copyright Supranational LLC\n' "$gf_comment"
        printf '%s Licensed under the Apache License, Version 2.0.\n' "$gf_comment"
        printf '%s SPDX-License-Identifier: Apache-2.0\n' "$gf_comment"
        printf '%s Modified by Zakura; generated from the attributed source.\n\n' "$gf_comment"
        "$perl_command" "$gf_source" "$gf_flavour"
    } > "$gf_destination"
    "$perl_command" -0pi -e 's/[ \t]+\n/\n/g; s/\n+\z/\n/' \
        "$gf_destination"
}

generate_tree() {
    tree_destination=$1
    mkdir -p "$tree_destination/elf" "$tree_destination/coff" \
        "$tree_destination/mach-o" "$tree_destination/win64"

    for generator in "$semolina"/asm/*-x86_64.pl; do
        base=$(basename "$generator" .pl)
        generate_file "$generator" masm "$tree_destination/win64/$base.asm" ";"
        generate_file "$generator" elf "$tree_destination/elf/$base.s" "#"
        generate_file "$generator" mingw64 "$tree_destination/coff/$base.s" "#"
        generate_file "$generator" macosx "$tree_destination/mach-o/$base.s" "#"
    done

    for generator in "$semolina"/asm/*-armv8.pl; do
        base=$(basename "$generator" .pl)
        generate_file "$generator" win64 "$tree_destination/win64/$base.asm" ";"
        generate_file "$generator" linux64 "$tree_destination/elf/$base.S" "//"
        generate_file "$generator" coff64 "$tree_destination/coff/$base.S" "//"
        generate_file "$generator" ios64 "$tree_destination/mach-o/$base.S" "//"
    done
}

if [ "${1:-}" = "--check" ]; then
    temporary=$(mktemp -d)
    trap 'rm -rf "$temporary"' EXIT HUP INT TERM
    generate_tree "$temporary"
    diff -ru "$semolina/elf" "$temporary/elf"
    diff -ru "$semolina/coff" "$temporary/coff"
    diff -ru "$semolina/mach-o" "$temporary/mach-o"
    diff -ru "$semolina/win64" "$temporary/win64"
elif [ "$#" -eq 0 ]; then
    generate_tree "$semolina"
else
    echo "usage: $0 [--check]" >&2
    exit 2
fi
