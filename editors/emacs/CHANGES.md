All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/),
and this project adheres to [Semantic Versioning](https://semver.org/).

## 01/02/2025

### Added
- Auto scroll to the first goal in the `Goals` buffer in case of many hypothesis
- Check that the Goals and Logs buffers are displayed before displaying logs and goals 

### Fixed
- Show the error at the end of file if any. That was not working because navigation stoped at the location of last command and not further (see issue #1111)