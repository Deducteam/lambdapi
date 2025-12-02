All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/),
and this project adheres to [Semantic Versioning](https://semver.org/).

## 01/02/2025

### Added
- Auto scroll to the first goal in the `Goals` buffer in case of many hypotheses
- Check that the Goals and Logs buffers are displayed before displaying logs and goals 
- Users can choose to underline either the entire command or just a part of it that is affected by the diagnostic.

### Fixed
- Show the error at the end of file if any. That was not working because navigation stopped at the location of last command and not further (see issue #1111)
- Irrelevant diagnostics (e.g. the one on the semicolon ending a symbol command) are removed.
- More relevant messages are associated to diagnostics instead of just `OK` messages.