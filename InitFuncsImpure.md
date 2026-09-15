/-
Array IO.FS.DirEntry
BaseIO (IO.Promise α)
BaseIO (Option String)
BaseIO (Task α)
BaseIO (Task β)
BaseIO Bool
BaseIO IO.FS.Stream
BaseIO IO.TaskState
BaseIO Nat
BaseIO UInt32
BaseIO UInt64
BaseIO Unit
BaseIO α
BaseIO β
Bool
ByteArray
IO
  (Prod cfg.stdin.toHandleType
    (IO.Process.Child { stdin := IO.Process.Stdio.null, stdout := cfg.stdout, stderr := cfg.stderr }))
IO (Array IO.FS.DirEntry)
IO (IO.Process.Child args.toStdioConfig)
IO (Option UInt32)
IO (Prod IO.FS.Handle System.FilePath)
IO Bool
IO ByteArray
IO IO.FS.Handle
IO IO.FS.Metadata
IO String
IO System.FilePath
IO UInt32
IO Unit
IO α
IO.FS.DirEntry
IO.FS.Handle
IO.FS.Metadata
IO.FS.Mode
IO.FS.Stream
IO.Process.Child args.toStdioConfig
IO.Process.Child cfg
IO.Process.Child { stdin := IO.Process.Stdio.null, stdout := cfg.stdout, stderr := cfg.stderr }
IO.Process.SpawnArgs
IO.Process.StdioConfig
IO.Promise α
IO.TaskState
List (Task α)
Nat
Option String
Option UInt32
PUnit
Prod IO.FS.Handle System.FilePath
Prod cfg.stdin.toHandleType
  (IO.Process.Child { stdin := IO.Process.Stdio.null, stdout := cfg.stdout, stderr := cfg.stderr })
ST σ (ST.Ref σ α)
ST σ Bool
ST σ Unit
ST σ α
ST.Ref σ α
String
System.FilePath
Task α
Task β
Task.Priority
UInt32
UInt64
UInt8
USize
Unit
cfg.stdin.toHandleType
-/

# Init/System/ST.lean

| name of extern     | def    | full name of func | type of func                                                            |
| ------------------ | ------ | ----------------- | ----------------------------------------------------------------------- |
| lean_st_mk_ref     | opaque | ST.Prim.mkRef     | {σ : Type} → {α : Type} → α → ST σ (ST.Ref σ α)                         |
| lean_st_ref_ptr_eq | opaque | ST.Prim.Ref.ptrEq | {σ : Type} → {α : Type} → (@& ST.Ref σ α) → (@& ST.Ref σ α) → ST σ Bool |
| lean_st_ref_get    | opaque | ST.Prim.Ref.get   | {σ : Type} → {α : Type} → (@& ST.Ref σ α) → ST σ α                      |
| lean_st_ref_swap   | opaque | ST.Prim.Ref.swap  | {σ : Type} → {α : Type} → (@& ST.Ref σ α) → α → ST σ α                  |
| lean_st_ref_take   | opaque | ST.Prim.Ref.take  | {σ : Type} → {α : Type} → (@& ST.Ref σ α) → ST σ α                      |
| lean_st_ref_put    | opaque | ST.Prim.Ref.put   | {σ : Type} → {α : Type} → (@& ST.Ref σ α) → α → ST σ Unit               |

# Init/System/IO.lean

| name of extern                   | def    | full name of func               | type of func                                                                                                                                                                                  |
| -------------------------------- | ------ | ------------------------------- | --------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- |
| lean_io_map_task                 | opaque | BaseIO.mapTask                  | {α : Type u_1} → {β : Type} → (α → BaseIO β) → Task α → optParam Task.Priority Task.Priority.default → optParam Bool Bool.false → BaseIO (Task β)                                             |
| lean_io_prim_handle_rewind       | opaque | IO.FS.Handle.rewind             | (@& IO.FS.Handle) → IO Unit                                                                                                                                                                   |
| lean_io_process_child_wait       | opaque | IO.Process.Child.wait           | {cfg : @& IO.Process.StdioConfig} → (@& IO.Process.Child cfg) → IO UInt32                                                                                                                     |
| lean_get_set_stderr              | opaque | IO.setStderr                    | IO.FS.Stream → BaseIO IO.FS.Stream                                                                                                                                                            |
| lean_io_prim_handle_is_tty       | opaque | IO.FS.Handle.isTty              | (@& IO.FS.Handle) → BaseIO Bool                                                                                                                                                               |
| lean_io_rename                   | opaque | IO.FS.rename                    | (@& System.FilePath) → (@& System.FilePath) → IO Unit                                                                                                                                         |
| lean_io_process_set_current_dir  | opaque | IO.Process.setCurrentDir        | (@& System.FilePath) → IO Unit                                                                                                                                                                |
| lean_io_get_num_heartbeats       | opaque | IO.getNumHeartbeats             | BaseIO Nat                                                                                                                                                                                    |
| lean_io_cancel                   | opaque | IO.cancel                       | {α : Type u_1} → (@& Task α) → BaseIO Unit                                                                                                                                                    |
| lean_io_allocprof                | opaque | allocprof                       | {α : Type} → (@& String) → IO α → IO α                                                                                                                                                        |
| lean_io_read_dir                 | opaque | System.FilePath.readDir         | (@& System.FilePath) → IO (Array IO.FS.DirEntry)                                                                                                                                              |
| lean_io_force_exit               | opaque | IO.Process.forceExit            | {α : Type} → UInt8 → IO α                                                                                                                                                                     |
| lean_io_prim_handle_mk           | opaque | IO.FS.Handle.mk                 | (@& System.FilePath) → IO.FS.Mode → IO IO.FS.Handle                                                                                                                                           |
| lean_io_wait_any                 | opaque | IO.waitAny                      | {α : Type} → (tasks : @& List (Task α)) → autoParam (GT.gt tasks.length 0) IO.waitAny._auto_1 → BaseIO α                                                                                      |
| lean_io_prim_handle_read         | opaque | IO.FS.Handle.read               | (@& IO.FS.Handle) → USize → IO ByteArray                                                                                                                                                      |
| lean_io_getenv                   | opaque | IO.getEnv                       | (@& String) → BaseIO (Option String)                                                                                                                                                          |
| lean_io_prim_handle_lock         | opaque | IO.FS.Handle.lock               | (@& IO.FS.Handle) → optParam Bool Bool.true → IO Unit                                                                                                                                         |
| lean_io_prim_handle_flush        | opaque | IO.FS.Handle.flush              | (@& IO.FS.Handle) → IO Unit                                                                                                                                                                   |
| lean_io_create_dir               | opaque | IO.FS.createDir                 | (@& System.FilePath) → IO Unit                                                                                                                                                                |
| lean_io_timeit                   | opaque | timeit                          | {α : Type} → (@& String) → IO α → IO α                                                                                                                                                        |
| lean_runtime_forget              | def    | Runtime.forget                  | {α : Sort u_1} → α → BaseIO Unit                                                                                                                                                              |
| lean_io_prim_handle_put_str      | opaque | IO.FS.Handle.putStr             | (@& IO.FS.Handle) → (@& String) → IO Unit                                                                                                                                                     |
| lean_io_app_path                 | opaque | IO.appPath                      | IO System.FilePath                                                                                                                                                                            |
| lean_io_mono_ms_now              | opaque | IO.monoMsNow                    | BaseIO Nat                                                                                                                                                                                    |
| lean_io_realpath                 | opaque | IO.FS.realPath                  | System.FilePath → IO System.FilePath                                                                                                                                                          |
| lean_io_process_child_take_stdin | opaque | IO.Process.Child.takeStdin      | {cfg : @& IO.Process.StdioConfig} → IO.Process.Child cfg → IO (Prod cfg.stdin.toHandleType (IO.Process.Child { stdin := IO.Process.Stdio.null, stdout := cfg.stdout, stderr := cfg.stderr })) |
| lean_io_remove_dir               | opaque | IO.FS.removeDir                 | (@& System.FilePath) → IO Unit                                                                                                                                                                |
| lean_io_prim_handle_truncate     | opaque | IO.FS.Handle.truncate           | (@& IO.FS.Handle) → IO Unit                                                                                                                                                                   |
| lean_io_as_task                  | opaque | BaseIO.asTask                   | {α : Type} → BaseIO α → optParam Task.Priority Task.Priority.default → BaseIO (Task α)                                                                                                        |
| lean_get_stdout                  | opaque | IO.getStdout                    | BaseIO IO.FS.Stream                                                                                                                                                                           |
| lean_io_metadata                 | opaque | System.FilePath.metadata        | (@& System.FilePath) → IO IO.FS.Metadata                                                                                                                                                      |
| lean_get_stdin                   | opaque | IO.getStdin                     | BaseIO IO.FS.Stream                                                                                                                                                                           |
| lean_io_hard_link                | opaque | IO.FS.hardLink                  | (@& System.FilePath) → (@& System.FilePath) → IO Unit                                                                                                                                         |
| lean_io_process_spawn            | opaque | IO.Process.spawn                | (args : IO.Process.SpawnArgs) → IO (IO.Process.Child args.toStdioConfig)                                                                                                                      |
| lean_io_prim_handle_get_line     | opaque | IO.FS.Handle.getLine            | (@& IO.FS.Handle) → IO String                                                                                                                                                                 |
| lean_io_get_tid                  | opaque | IO.getTID                       | BaseIO UInt64                                                                                                                                                                                 |
| lean_io_process_child_try_wait   | opaque | IO.Process.Child.tryWait        | {cfg : @& IO.Process.StdioConfig} → (@& IO.Process.Child cfg) → IO (Option UInt32)                                                                                                            |
| lean_io_set_heartbeats           | opaque | IO.setNumHeartbeats             | Nat → BaseIO Unit                                                                                                                                                                             |
| lean_runtime_hold                | def    | Runtime.hold                    | {α : Sort u_1} → (@& α) → BaseIO Unit                                                                                                                                                         |
| lean_io_prim_handle_write        | opaque | IO.FS.Handle.write              | (@& IO.FS.Handle) → (@& ByteArray) → IO Unit                                                                                                                                                  |
| lean_io_get_random_bytes         | opaque | IO.getRandomBytes               | USize → IO ByteArray                                                                                                                                                                          |
| lean_io_bind_task                | opaque | BaseIO.bindTask                 | {α : Type u_1} → {β : Type} → Task α → (α → BaseIO (Task β)) → optParam Task.Priority Task.Priority.default → optParam Bool Bool.false → BaseIO (Task β)                                      |
| lean_io_prim_handle_unlock       | opaque | IO.FS.Handle.unlock             | (@& IO.FS.Handle) → IO Unit                                                                                                                                                                   |
| lean_io_create_tempfile          | opaque | IO.FS.createTempFile            | IO (Prod IO.FS.Handle System.FilePath)                                                                                                                                                        |
| lean_io_check_canceled           | opaque | IO.checkCanceled                | BaseIO Bool                                                                                                                                                                                   |
| lean_io_initializing             | opaque | IO.initializing                 | BaseIO Bool                                                                                                                                                                                   |
| lean_runtime_mark_multi_threaded | def    | Runtime.markMultiThreaded       | {α : Type} → α → BaseIO α                                                                                                                                                                     |
| lean_io_create_tempdir           | opaque | IO.FS.createTempDir             | IO System.FilePath                                                                                                                                                                            |
| lean_io_get_task_state           | opaque | IO.getTaskState                 | {α : Type u_1} → (@& Task α) → BaseIO IO.TaskState                                                                                                                                            |
| lean_runtime_mark_persistent     | def    | Runtime.markPersistent          | {α : Type} → α → BaseIO α                                                                                                                                                                     |
| lean_get_set_stdin               | opaque | IO.setStdin                     | IO.FS.Stream → BaseIO IO.FS.Stream                                                                                                                                                            |
| lean_io_process_get_pid          | opaque | IO.Process.getPID               | BaseIO UInt32                                                                                                                                                                                 |
| lean_io_exit                     | opaque | IO.Process.exit                 | {α : Type} → UInt8 → IO α                                                                                                                                                                     |
| lean_chmod                       | opaque | IO.Prim.setAccessRights         | (@& System.FilePath) → UInt32 → IO Unit                                                                                                                                                       |
| lean_io_prim_handle_try_lock     | opaque | IO.FS.Handle.tryLock            | (@& IO.FS.Handle) → optParam Bool Bool.true → IO Bool                                                                                                                                         |
| lean_io_remove_file              | opaque | IO.FS.removeFile                | (@& System.FilePath) → IO Unit                                                                                                                                                                |
| lean_get_set_stdout              | opaque | IO.setStdout                    | IO.FS.Stream → BaseIO IO.FS.Stream                                                                                                                                                            |
| lean_io_symlink_metadata         | opaque | System.FilePath.symlinkMetadata | (@& System.FilePath) → IO IO.FS.Metadata                                                                                                                                                      |
| lean_get_stderr                  | opaque | IO.getStderr                    | BaseIO IO.FS.Stream                                                                                                                                                                           |
| lean_io_process_child_kill       | opaque | IO.Process.Child.kill           | {cfg : @& IO.Process.StdioConfig} → (@& IO.Process.Child cfg) → IO Unit                                                                                                                       |
| lean_io_process_get_current_dir  | opaque | IO.Process.getCurrentDir        | IO System.FilePath                                                                                                                                                                            |
| lean_io_current_dir              | opaque | IO.currentDir                   | IO System.FilePath                                                                                                                                                                            |
| lean_io_wait                     | opaque | IO.wait                         | {α : Type} → Task α → BaseIO α                                                                                                                                                                |
| lean_io_mono_nanos_now           | opaque | IO.monoNanosNow                 | BaseIO Nat                                                                                                                                                                                    |

# Init/System/Promise.lean

| name of extern          | def    | full name of func  | type of func                                      |
| ----------------------- | ------ | ------------------ | ------------------------------------------------- |
| lean_io_promise_new     | opaque | IO.Promise.new     | {α : Type} → [Nonempty α] → BaseIO (IO.Promise α) |
| lean_io_promise_resolve | opaque | IO.Promise.resolve | {α : Type} → α → (@& IO.Promise α) → BaseIO Unit  |

