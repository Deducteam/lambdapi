| Library        | Lambdapi time | Lambdapi RAM | Dedukti time | Dedukti RAM |
| -------------- | ------------- | ------------ | ------------ | ----------- |
| focalide       |         00:05 |        236Mb |        00:08 |        44Mb |
| holide         |         02:18 |       1347Mb |        01:52 |       527Mb |
| iprover        |         03:30 |         88Mb |        02:38 |        82Mb |
| matita         |         15:57 |        403Mb |        13:08 |       160Mb |
| verine         |         00:31 |        738Mb |        00:49 |       659Mb |
| zenon modulo   |         36:45 |       1547Mb |        09:47 |       820Mb |

Remarks:
 - Tests for zenon ran with 28 CPUs, others were run on a single CPU.
 - 128 files (over 6766) were blacklisted for iprover with Lambdapi.
