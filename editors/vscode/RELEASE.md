TODO list for a new release on the VSCode Marketplace
-----------------------------------------------------

See the details [here](https://code.visualstudio.com/api/working-with-extensions/publishing-extension).

- Check the rendering of README.md in some [Markdown viewer](https://codebeautify.org/markdown-viewer). It will be displayed in VSCode by going to extensions
(Ctrl+Shift+X) and by clicking on lambdapi.

- Create a new Personal Access Token on [Azure](https://dev.azure.com/lambdapi/) and save it into a file.

- Publish a new version on the Marketplace:

```bash
vsce login lambdapi # and paste the Personal Access Token
vsce publish [patch|minor|major]
```

The publisher page is [here](https://marketplace.visualstudio.com/manage/publishers/deducteam).
