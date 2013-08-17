#!/bin/bash

DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" && pwd )"
pushd "$DIR" 1>/dev/null

if [ -z "$SSHKEY_PASSWORD" ]; then
    echo 'Error: no $SSHKEY_PASSWORD variable present'
    exit 1
fi

touch ./ssh.sh
SSH_SH="$DIR/ssh.sh"


echo "Making ssh.sh at '$SSH_SH'"
echo '#!/bin/sh' > $SSH_SH
echo 'exec ssh -o StrictHostKeyChecking=no -i "'"$DIR/id_rsa"'" "$@"' >> $SSH_SH
chmod +x $SSH_SH
export GIT_SSH="$SSH_SH"
echo "Decrypting id_rsa..."
openssl aes-256-cbc -k "$SSHKEY_PASSWORD" -in id_rsa.enc -d -a -out id_rsa
chmod 0600 id_rsa

popd 1>/dev/null
