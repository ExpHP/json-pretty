// FIXME: Bunch of cruft to delete from here, this was copied from truth's decompiler

use thiserror::Error;
use std::io::{self, Write};
use serde_json::value::Value;

/// Trait for pretty-printing values.
///
/// This is not provided via [`std::fmt::Display`] because additional pretty-printing
/// state must be tracked.  Error messages wishing to display something may use the
/// [`stringify`] function.
///
/// Typically you do not need to import this if you want to display stuff; instead,
/// construct a [`Formatter`] and use the [`Formatter::fmt`] inherent method.
pub trait Format {
    fn fmt<W: Write>(&self, out: &mut Formatter<W>) -> Result;
}

/// Write a value to string, for `eprintln` debugging.
///
/// Defaults to a fairly large max width, mostly to reduce console spam for `eprintln`.
pub fn stringify<T: Format>(value: &T) -> String {
    stringify_with(value, Config::new().max_columns(1000))
}

/// Write a value to string, for `eprintln` debugging and `insta` tests.
pub fn stringify_with<T: Format>(value: &T, config: Config) -> String {
    let mut f = Formatter::with_config(vec![], config);
    f.fmt(value).expect("failed to write to vec!?");
    String::from_utf8_lossy(&f.into_inner().unwrap()).into_owned()
}

//==============================================================================

pub type Result<T = ()> = std::result::Result<T, Error>;

#[derive(Debug, Error)]
#[error(transparent)]
pub struct Error(ErrorKind);

#[derive(Debug, Error)]
enum ErrorKind {
    #[error("{}", .0)]
    Io(io::Error),

    // This variant is used to implement backtracking for things with conditional block formatting.
    // If the user ever sees this error message, it's because the error must have somehow been
    // unwrapped instead of backtracking.
    #[error("Failed to backtrack for conditional block formatting. This is a bug!")]
    LineBreakRequired,
}

impl From<io::Error> for Error {
    fn from(e: io::Error) -> Self { Error(ErrorKind::Io(e)) }
}

//==============================================================================

#[derive(Debug, Clone)]
pub struct Config {
    target_width: usize,
}

impl Default for Config {
    fn default() -> Self {
        Config {
            target_width: 99,
        }
    }
}

impl Config {
    pub fn new() -> Self {
        Default::default()
    }

    /// Set the target maximum line length for formatting.
    ///
    /// The formatter will generally try to break lines to be within this length,
    /// though there is no guarantee.
    pub fn max_columns(mut self, width: usize) -> Self {
        // FIXME: The -1 is to work around a known bug where, if something is in
        //        block mode and one of its items exactly hits the target_width in
        //        inline mode, then the comma after the item will surpass the width
        //        without triggering backtracking on the item.
        self.target_width = width - 1; self
    }
}

//==============================================================================

pub use formatter::{Formatter};

mod formatter {
    use super::*;

    const INDENT: isize = 4;

    /// Type that manages the formatting and display of AST nodes.
    ///
    /// It contains and manages state related to indentation and block formatting.
    pub struct Formatter<W: io::Write> {
        // This is an Option only so that `into_inner` can remove it.
        writer: Option<W>,
        // User config
        pub(super) config: Config,
        // Block- and line- formatting state
        pending_data: bool,
        line_buffer: Vec<u8>,
        indent: usize,
        inline_depth: u32,
    }

    /// If a partially-written line has not yet been committed through a call to
    /// [`Formatter::next_line`], it will be written on drop, and errors will be ignored.
    impl<W: io::Write> Drop for Formatter<W> {
        fn drop(&mut self) {
            let _ = self._flush_incomplete_line();
        }
    }

    impl<W: io::Write> Formatter<W> {
        /// Construct a new [`Formatter`] for writing at an initial indent level of 0.
        pub fn new(writer: W) -> Self {
            Self::with_config(writer, Config::new())
        }

        /// Construct a new [`Formatter`] for writing at an initial indent level of 0.
        pub fn with_config(writer: W, config: Config) -> Self {
            Self {
                writer: Some(writer),
                config,
                indent: 0,
                inline_depth: 0,
                pending_data: false,
                // The initial level here is used when writing a Stmt as toplevel.
                // When parsing items, we mostly use a second level that gets pushed/popped with functions.
                line_buffer: vec![],
            }
        }

        /// Recover the wrapped `io::Write` object.
        ///
        /// **Important:** If the last line has not yet been written by calling
        /// [`Formatter::next_line`], it will attempt to write this data now.
        /// This can fail, hence the `Result`.
        pub fn into_inner(mut self) -> Result<W> {
            self._flush_incomplete_line()?;
            Ok(self.writer.take().unwrap())
        }

        fn _flush_incomplete_line(&mut self) -> Result {
            if self.pending_data {
                self.writer.as_mut().unwrap().write_all(&self.line_buffer)?;
                self.pending_data = false;
            }
            Ok(())
        }
    }

    impl<W: io::Write> Formatter<W> {
        /// Convenience method that calls [`Format::fmt`].
        pub fn fmt<T: Format>(&mut self, x: T) -> Result { x.fmt(self) }

        /// Write a line without any indent, like a label.
        ///
        /// Only works at the beginning of the line (otherwise it just writes normally,
        /// followed by a space).  When it does take effect, a newline is automatically
        /// inserted after writing the argument.
        pub fn fmt_label<T: Format>(&mut self, label: T) -> Result {
            if self.pending_data {
                // write label inline
                self.fmt((label, " "))?;
            } else {
                // write label flush with margin
                self.line_buffer.clear(); // strip indent
                self.fmt(label)?;
                self.next_line()?;
            }
            Ok(())
        }

        /// Write a comma-separated list.
        ///
        /// Switches to block style (with trailing comma) on long lines.
        pub fn fmt_comma_separated<T, Ts>(
            &mut self,
            open: &'static str,
            close: &'static str,
            get_items: impl Fn() -> Ts,
        ) -> Result
        where
            T: Format,
            Ts: ExactSizeIterator<Item=T>,
        {
            self.try_inline(|me| {
                // Reasons the inline formatting may fail:
                // * A line length check may fail here.
                // * One of the list items may unconditionally produce a newline
                me.fmt(open)?;
                let mut first = true;
                for x in get_items() {
                    if !first { me.fmt(", ")?; }
                    first = false;
                    me.fmt(x)?;
                    me.backtrack_inline_if_long()?;
                }
                me.fmt(close)?;
                me.backtrack_inline_if_long()
            }, |me| {
                // Block formatting
                me.fmt(open)?;
                me.next_line()?;
                me.indent()?;

                let items = get_items();
                let item_count = items.len();
                for (index, x) in items.enumerate() {
                    me.fmt(x)?;
                    if index != item_count - 1 {
                        me.fmt(",")?;
                    }
                    me.next_line()?;
                }
                me.dedent()?;
                me.fmt(close)
            })
        }

        /// Helper which writes items from an iterator, invoking the separator closure between
        /// each pair of items. (but NOT after the final item)
        pub fn fmt_separated<T: Format, B>(
            &mut self,
            items: impl IntoIterator<Item=T> + Clone,
            mut sep: impl FnMut(&mut Self) -> Result<B>,
        ) -> Result {
            let mut first = true;
            for x in items {
                if !first { sep(self)?; }
                first = false;
                self.fmt(x)?;
            }
            Ok(())
        }

        /// Increases the indent level.
        ///
        /// Panics if not at the beginning of a line.
        pub fn indent(&mut self) -> Result { self._add_indent(INDENT) }

        /// Decreases the indent level.
        ///
        /// Panics if not at the beginning of a line, or if an attempt is made to dedent beyond the
        /// left margin.
        pub fn dedent(&mut self) -> Result { self._add_indent(-INDENT) }

        /// Output a line and start a new one at the same indent level.  Causes backtracking
        /// if currently in inline mode.
        pub fn next_line(&mut self) -> Result {
            self.backtrack_inline()?;
            if !self.pending_data {
                self.line_buffer.truncate(0);  // don't emit trailing spaces on a blank line
            }

            self.pending_data = false;
            self.line_buffer.push(b'\n');
            self.writer.as_mut().unwrap().write_all(&self.line_buffer)?;
            self.line_buffer.clear();
            self.line_buffer.resize(self.indent, b' ');
            Ok(())
        }

        // ---------------------

        /// Appends a string to the current (not yet written) line.
        pub(super) fn append_to_line(&mut self, bytes: &[u8]) -> Result {
            // Catch accidental use of "\n" in output strings where next_line() should be used.
            assert!(!bytes.contains(&b'\n'), "Tried to append newline to line. This is a bug!");
            self.line_buffer.extend_from_slice(bytes);
            self.write_occurred();
            Ok(())
        }

        /// Append to the current (not yet written) line using [`std::fmt::Display`].
        pub(super) fn append_display_to_line(&mut self, x: impl std::fmt::Display) -> Result {
            write!(&mut self.line_buffer, "{}", x)?;
            self.write_occurred();
            Ok(())
        }

        fn write_occurred(&mut self) {
            self.pending_data = true;
        }

        /// If we're in inline mode, backtrack to the outermost [`Formatter::try_inline`].
        fn backtrack_inline(&mut self) -> Result {
            if self.inline_depth > 0 {
                return Err(Error(ErrorKind::LineBreakRequired));
            }
            Ok(())
        }

        /// If we're in inline mode and the line is too long, backtrack to the
        /// outermost [`Formatter::try_inline`].
        fn backtrack_inline_if_long(&mut self) -> Result {
            if self.inline_depth > 0 && self.line_buffer.len() > self.config.target_width {
                return Err(Error(ErrorKind::LineBreakRequired));
            }
            Ok(())
        }

        /// Attempt to write something inline, else write block style.
        fn try_inline<B>(
            &mut self,
            mut inline_cb: impl FnMut(&mut Self) -> Result<B>,
            mut block_cb: impl FnMut(&mut Self) -> Result<B>,
        ) -> Result<B> {
            let backtrack_pos = match self.inline_depth {
                0 => Some(self.line_buffer.len()),
                _ => None, // don't backtrack if nested in another inline_cb
            };
            self.inline_depth += 1;
            let result = inline_cb(self);
            self.inline_depth -= 1;
            match (result, backtrack_pos) {
                // If we fail to write inline and this is the outermost `try_inline`,
                // backtrack and try writing not inline.
                (Err(Error(ErrorKind::LineBreakRequired)), Some(backtrack_pos)) => {
                    assert_eq!(self.inline_depth, 0, "Block cb in inline mode. This is a bug!");
                    self.line_buffer.truncate(backtrack_pos);
                    block_cb(self)
                },
                (result, _) => result,
            }
        }

        fn _add_indent(&mut self, delta: isize) -> Result {
            let new_indent = self.indent as isize + delta;
            assert!(!self.pending_data, "Attempted to change indent mid-line. This is a bug!");
            assert!(new_indent >= 0, "Attempted to dedent past 0. This is a bug!");

            self.indent = new_indent as usize;
            self.line_buffer.resize(self.indent, b' ');
            Ok(())
        }
    }
}

enum Either<A, B> { This(A), That(B) }

impl<A: Format, B: Format> Format for Either<A, B> {
    fn fmt<W: Write>(&self, out: &mut Formatter<W>) -> Result {
        match self {
            Either::This(x) => out.fmt(x),
            Either::That(x) => out.fmt(x),
        }
    }
}

//==============================================================================

// Base impls: To write arbitrary text, use a string type.
impl Format for String {
    fn fmt<W: Write>(&self, out: &mut Formatter<W>) -> Result {
        Format::fmt(&**self, out)
    }
}

impl Format for str {
    fn fmt<W: Write>(&self, out: &mut Formatter<W>) -> Result {
        out.append_to_line(self.as_ref())
    }
}

// Use `format_args!` to delegate to a `std::fmt` trait.
impl Format for std::fmt::Arguments<'_> {
    fn fmt<W: Write>(&self, out: &mut Formatter<W>) -> Result {
        out.append_display_to_line(self)
    }
}

// Forwarded impls
impl<T: Format + ?Sized> Format for &T {
    fn fmt<W: Write>(&self, out: &mut Formatter<W>) -> Result {
        Format::fmt(&**self, out)
    }
}
impl<T: Format + ?Sized> Format for &mut T {
    fn fmt<W: Write>(&self, out: &mut Formatter<W>) -> Result {
        Format::fmt(&**self, out)
    }
}
impl<T: Format + ?Sized> Format for Box<T> {
    fn fmt<W: Write>(&self, out: &mut Formatter<W>) -> Result {
        Format::fmt(&**self, out)
    }
}

//==============================================================================

/// Additional state used during formatting which is not directly related to indentation and
/// block formatting.
#[derive(Debug, Clone)]
struct State {
    /// When we are printing instructions, tracks the last time label so that we can produce a
    /// nice listing with relative labels.
    ///
    /// A stack is used *as if* we supported nested function definitions.  In practice, the level at
    /// index 0 gets used exclusively when writing `Stmt`s, and a level at index 1 gets used when
    /// writing `Item`s.
    time_stack: Vec<i32>,

    /// Used to control grouping of `interrupt[n]:` lines.
    prev_line_was_interrupt: bool,
}

impl State {
    fn new() -> Self { State {
        time_stack: vec![0],
        prev_line_was_interrupt: false,
    }}
}

//==============================================================================
// Helpers

// Tuples concatenate their arguments.
//
// The most important use case is to facilitate use of helper functions that take
// `impl IntoIterator<T> where T: Format`.  As a small bonus, it also helps
// reduce verbosity in plain `fmt` calls.
macro_rules! impl_tuple_format {
    ($($a:ident:$A:ident),*) => {
        impl<$($A: Format),*> Format for ( $($A),* ) {
            fn fmt<W: Write>(&self, out: &mut Formatter<W>) -> Result {
                let ( $($a),* ) = self;
                $( Format::fmt($a, out)?; )*
                Ok(())
            }
        }
    }
}

impl_tuple_format!(a:A, b:B);
impl_tuple_format!(a:A, b:B, c:C);
impl_tuple_format!(a:A, b:B, c:C, d:D);
impl_tuple_format!(a:A, b:B, c:C, d:D, e:E);
impl_tuple_format!(a:A, b:B, c:C, d:D, e:E, f:F);
impl_tuple_format!(a:A, b:B, c:C, d:D, e:E, f:F, g:G);
impl_tuple_format!(a:A, b:B, c:C, d:D, e:E, f:F, g:G, h:H);

//==============================================================================
// Items

struct JsonString<S: AsRef<str>>(S);

impl<S: AsRef<str>> Format for JsonString<S> {
    fn fmt<W: Write>(&self, out: &mut Formatter<W>) -> Result {
        // FIXME can this allocation be avoided?
        let rendered = serde_json::to_string(self.0.as_ref()).unwrap();
        out.fmt(rendered)
    }
}

impl Format for Value {
    fn fmt<W: Write>(&self, out: &mut Formatter<W>) -> Result {
        match self {
            Value::Array(array) => {
                out.fmt_comma_separated("[", "]", || array.iter())
            },
            Value::Object(object) => {
                out.fmt_comma_separated("{", "}", || object.iter().map(|(k, v)| (JsonString(k), ": ", v)))
            },

            Value::Null => out.fmt("null"),
            Value::Bool(true) => out.fmt("true"),
            Value::Bool(false) => out.fmt("false"),

            | Value::Number { .. }
            | Value::String { .. }
            => {
                // FIXME can this allocation be avoided?
                let rendered = serde_json::to_string(self).unwrap();
                out.fmt(rendered)
            }
        }
    }
}
