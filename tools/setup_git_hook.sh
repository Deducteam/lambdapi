#!/bin/sh

set -euf

dir=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
git_root="$(realpath "${dir}/../.git")"

user_hook=''
hook_path="${git_root}/hooks/pre-commit"
hook_merge='#!/bin/sh
${GIT_DIR}/hooks/pre-commit-user
${GIT_DIR}/hooks/pre-commit-lambdapi
'
hook_lambdapi='#!/bin/sh
[ -z "$(make sanity_check)" ]
'

if [ -f "${hook_path}" ]; then
    user_hook=true
    if grep -q 'sanity_check' "${hook_path}" || \
        grep -q 'pre-commit-lambdapi' "${hook_path}"; then
        # Hook already set up
        printf "Pre-commit hook already set up.\\n"
        exit 0
    fi
    printf "Moving existing pre-commit hook to '%s'\\n" \
        "${hook_path}-user"
    mv "${hook_path}" "${hook_path}-user"
fi

if [ -n "${user_hook}" ]; then
    printf "%s" "${hook_merge}" > "${hook_path}"
    printf "%s" "${hook_lambdapi}" > "${hook_path}-lambdapi"
else
    printf "%s" "${hook_lambdapi}" > "${hook_path}"
fi
