# typed-video [![Build Status](https://travis-ci.org/videolang/typed-video.svg?branch=master)](https://travis-ci.org/videolang/typed-video)

### Notes for this branch (`types-with-stop-list`)

This branch experiments with changing `type-eval` to expand types with stop-list, rather than fully.

This makes `type-eval` more convenient for types that are lifted terms, but imposes more work for existing types.

Specifically, the arguments to type constructors must be manually `type-eval`ed.
- the `~Any/eval` constructor currently performs this task
- currently, the recursive calls to `type-eval` do not carry a context, so this approach
  is not working for binding types



A prototype typed version of `#lang video`
