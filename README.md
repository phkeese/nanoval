# nanoval - A NaN-tagged value

This library provides an implementation of a NaN-tagged value supporting `f64`, `bool`, `i32`, `u32`, null-values and a
subset of pointers.
Each value is only 8 bytes in size and uses the large space of NaN values to store additional information inside a
single
64 bit double precision floating point value.

This implementation is heavily inspired by the [Wren programming language](https://wren.io/), although it does differ in
some aspects.

If you find a bug or have ideas for improvements, please open an issue or a pull request.

I hope you find this library useful!

## Usage

The `Value` type can be constructed from `f64`, `bool`, `i32`, `u32`, `()` and pointers and references to arbitrary `T`:

```rust
use nanoval::Value;

let double = Value::from(3.14);
let integer = Value::from(42);
let boolean = Value::from(true);
let null = Value::from(());
let pointer = Value::from( & 42);
```

The constructed value can be converted back to the original type:

```rust
assert_eq!(double.as_f64(), Some(3.14));
assert_eq!(integer.as_i32(), Some(42));
assert_eq!(boolean.as_bool(), Some(true));
assert!(null.is_null());
assert_eq!(pointer.as_pointer::<i32>(), Some(&42 as *const i32));
```
