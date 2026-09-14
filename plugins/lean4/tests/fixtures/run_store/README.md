Prebuilt run-store/v1 run for the portable read-only `load` tests (tests/test_run_store.py `PortableLoad`, also run on the Windows CI job). Regenerate with the store, then pin `ts`/`storage_root`/`plugin_version` as in the generator; the store's own `runs/.gitignore` is deliberately absent here so the fixture is tracked.

A second run written with `--event-schema run-store-event/v2` (#82B) carries `review` and `replan` events; the v1 run must keep loading unchanged beside it.
