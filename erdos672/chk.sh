#!/bin/bash
# usage: chk.sh File.lean [build]   (build => also write build/File.olean)
export PATH=$HOME/.elan/bin:$PATH
f=$1; m=${f%.lean}
cd /opt/oma/.oma/formal-conjectures && lake env bash -c "cd /home/user/lean/erdos672 && LEAN_PATH=\$LEAN_PATH:/home/user/lean/erdos672/build lean --root=. $( [ "$2" = build ] && echo "-o build/$m.olean" ) $f"
