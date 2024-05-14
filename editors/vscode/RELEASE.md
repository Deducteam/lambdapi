TODO list for a new release on the VSCode Marketplace
-----------------------------------------------------
**Release from pipeline**

The github DICD pipeline detects the existance of a new version of the Lambdapi extension for Vscode based on the `version` field in the `editors/vscode/package.json` file and publishes it on the Marketplace.

Please note that a valid Azure Personal Access Token (PAT) is required for this operation. This PAT must be saved in the `VSCODE_PAT` environment variable as described [here](https://docs.github.com/en/actions/security-guides/using-secrets-in-github-actions).

If the pipeline fails at publishing the extension, it may be due to the PAT being expired.
Please generate a new one on [Azure](https://dev.azure.com/lambdapi/) and update the `VSCODE_PAT` env variable value as described in the link above.

**manual release**

Though it is not recommanded, it is still possible to manually publish a new version on the marketplace as described bellow 
(See the details [here](https://code.visualstudio.com/api/working-with-extensions/publishing-extension)).

- Check the rendering of README.md in some [Markdown viewer](https://codebeautify.org/markdown-viewer). It will be displayed in VSCode by going to extensions
(Ctrl+Shift+X) and by clicking on lambdapi.

- Create a new Personal Access Token on [Azure](https://dev.azure.com/lambdapi/) and save it into a file.

- Publish a new version on the Marketplace:

```bash
make
vsce login Deducteam # and paste the Personal Access Token
vsce publish [patch|minor|major]
```

The publisher page is [here](https://marketplace.visualstudio.com/manage/publishers/deducteam).
