use core::fmt;
use core::iter::FusedIterator;
use core::str::pattern::{DoubleEndedSearcher, Pattern, ReverseSearcher, Searcher};

pub struct Splitter<'a, P: Pattern<'a>> {
    internal: SplitInternal<'a, P>,
}

impl<'a, P> Clone for Splitter<'a, P>
where
    P: Pattern<'a, Searcher: Clone>,
{
    fn clone(&self) -> Self {
        Splitter {
            internal: self.internal.clone(),
        }
    }
}

impl<'a, P> fmt::Debug for Splitter<'a, P>
where
    P: Pattern<'a, Searcher: fmt::Debug>,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Splitter")
            .field("internal", &self.internal)
            .finish()
    }
}

impl<'a, P: Pattern<'a>> Iterator for Splitter<'a, P> {
    type Item = &'a str;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        self.internal.next()
    }
}
impl<'a, P: Pattern<'a>> DoubleEndedIterator for Splitter<'a, P>
where
    P::Searcher: DoubleEndedSearcher<'a>,
{
    #[inline]
    fn next_back(&mut self) -> Option<Self::Item> {
        self.internal.next_back()
    }
}
impl<'a, P: Pattern<'a>> FusedIterator for Splitter<'a, P> where Splitter<'a, P>: Iterator {}

impl<'a, P: Pattern<'a>> Splitter<'a, P> {
    /// Splits the string on the first occurrence of the specified delimiter and
    /// returns prefix before delimiter and suffix after delimiter.
    ///
    /// # Examples
    ///
    /// ```
    /// # use str_splitter::combinators::SplitExt;
    /// assert_eq!("cfg".splitter('=').once(), None);
    /// assert_eq!("cfg=".splitter('=').once(), Some(("cfg", "")));
    /// assert_eq!("cfg=foo".splitter('=').once(), Some(("cfg", "foo")));
    /// assert_eq!("cfg=foo=bar".splitter('=').once(), Some(("cfg", "foo=bar")));
    /// ```
    #[inline]
    pub fn once(self) -> Option<(&'a str, &'a str)> {
        self.internal.once()
    }

    /// An iterator over substrings of the given string slice, separated by
    /// characters matched by a pattern.
    ///
    /// The [pattern] can be a `&str`, [`char`], a slice of [`char`]s, or a
    /// function or closure that determines if a character matches.
    ///
    /// [`char`]: prim@char
    /// [pattern]: self::pattern
    ///
    /// Equivalent to [`split`], except that the trailing substring
    /// is skipped if empty.
    ///
    /// [`split`]: str::split
    ///
    /// This method can be used for string data that is _terminated_,
    /// rather than _separated_ by a pattern.
    ///
    /// # Iterator behavior
    ///
    /// The returned iterator will be a [`DoubleEndedIterator`] if the pattern
    /// allows a reverse search and forward/reverse search yields the same
    /// elements. This is true for, e.g., [`char`], but not for `&str`.
    ///
    /// If the pattern allows a reverse search but its results might differ
    /// from a forward search, the [`rsplit_terminator`] method can be used.
    ///
    /// [`rsplit_terminator`]: str::rsplit_terminator
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// # use str_splitter::combinators::SplitExt;
    /// let v: Vec<&str> = "A.B.".splitter('.').to_terminated().collect();
    /// assert_eq!(v, ["A", "B"]);
    ///
    /// let v: Vec<&str> = "A..B..".splitter(".").to_terminated().collect();
    /// assert_eq!(v, ["A", "", "B", ""]);
    ///
    /// let v: Vec<&str> = "A.B:C.D".splitter(&['.', ':'][..]).to_terminated().collect();
    /// assert_eq!(v, ["A", "B", "C", "D"]);
    /// ```
    pub fn to_terminated(mut self) -> Self {
        self.internal.allow_trailing_empty = false;
        self
    }

    /// An iterator over substrings of this string slice, separated by
    /// characters matched by a pattern. Differs from the iterator produced by
    /// `split` in that `split_inclusive` leaves the matched part as the
    /// terminator of the substring.
    ///
    /// The [pattern] can be a `&str`, [`char`], a slice of [`char`]s, or a
    /// function or closure that determines if a character matches.
    ///
    /// [`char`]: prim@char
    /// [pattern]: self::pattern
    ///
    /// # Examples
    ///
    /// ```
    /// # use str_splitter::combinators::SplitExt;
    /// let v: Vec<&str> = "Mary had a little lamb\nlittle lamb\nlittle lamb."
    ///     .splitter('\n').to_inclusive().collect();
    /// assert_eq!(v, ["Mary had a little lamb\n", "little lamb\n", "little lamb."]);
    /// ```
    ///
    /// If the last element of the string is matched,
    /// that element will be considered the terminator of the preceding substring.
    /// That substring will be the last item returned by the iterator.
    ///
    /// ```
    /// # use str_splitter::combinators::SplitExt;
    /// let v: Vec<&str> = "Mary had a little lamb\nlittle lamb\nlittle lamb.\n"
    ///     .splitter('\n').to_inclusive().collect();
    /// assert_eq!(v, ["Mary had a little lamb\n", "little lamb\n", "little lamb.\n"]);
    /// ```
    pub fn to_inclusive(self) -> Inclusive<Splitter<'a, P>> {
        let mut internal = self.internal;
        internal.allow_trailing_empty = false;

        Inclusive(Splitter { internal })
    }

    /// An iterator over substrings of the given string slice, separated by
    /// characters matched by a pattern and yielded in reverse order.
    ///
    /// The [pattern] can be a `&str`, [`char`], a slice of [`char`]s, or a
    /// function or closure that determines if a character matches.
    ///
    /// [`char`]: prim@char
    /// [pattern]: self::pattern
    ///
    /// # Iterator behavior
    ///
    /// The returned iterator requires that the pattern supports a reverse
    /// search, and it will be a [`DoubleEndedIterator`] if a forward/reverse
    /// search yields the same elements.
    ///
    /// For iterating from the front, the [`split`] method can be used.
    ///
    /// [`split`]: str::split
    ///
    /// # Examples
    ///
    /// Simple patterns:
    ///
    /// ```
    /// # use str_splitter::combinators::SplitExt;
    /// let v: Vec<&str> = "Mary had a little lamb".splitter(' ').to_reversed().collect();
    /// assert_eq!(v, ["lamb", "little", "a", "had", "Mary"]);
    ///
    /// let v: Vec<&str> = "".splitter('X').to_reversed().collect();
    /// assert_eq!(v, [""]);
    ///
    /// let v: Vec<&str> = "lionXXtigerXleopard".splitter('X').to_reversed().collect();
    /// assert_eq!(v, ["leopard", "tiger", "", "lion"]);
    ///
    /// let v: Vec<&str> = "lion::tiger::leopard".splitter("::").to_reversed().collect();
    /// assert_eq!(v, ["leopard", "tiger", "lion"]);
    /// ```
    ///
    /// A more complex pattern, using a closure:
    ///
    /// ```
    /// # use str_splitter::combinators::SplitExt;
    /// let v: Vec<&str> = "abc1defXghi".splitter(|c| c == '1' || c == 'X').to_reversed().collect();
    /// assert_eq!(v, ["ghi", "def", "abc"]);
    /// ```
    ///
    ///
    /// ```compile_fail
    /// # use str_splitter::combinators::SplitExt;
    /// // should not implement DoubleEndedIterator
    /// fn reverse(input: &str) -> impl DoubleEndedIterator {
    ///     input.splitter("aa").to_reversed()
    /// }
    /// ```
    pub fn to_reversed(self) -> Reversed<Splitter<'a, P>>
    where
        P::Searcher: ReverseSearcher<'a>,
    {
        Reversed(self)
    }

    /// An iterator over substrings of the given string slice, separated by a
    /// pattern, restricted to returning at most `n` items.
    ///
    /// If `n` substrings are returned, the last substring (the `n`th substring)
    /// will contain the remainder of the string.
    ///
    /// The [pattern] can be a `&str`, [`char`], a slice of [`char`]s, or a
    /// function or closure that determines if a character matches.
    ///
    /// [`char`]: prim@char
    /// [pattern]: self::pattern
    ///
    /// # Iterator behavior
    ///
    /// The returned iterator will not be double ended, because it is
    /// not efficient to support.
    ///
    /// If the pattern allows a reverse search, the [`rsplitn`] method can be
    /// used.
    ///
    /// [`rsplitn`]: str::rsplitn
    ///
    /// # Examples
    ///
    /// Simple patterns:
    ///
    /// ```
    /// # use str_splitter::combinators::SplitExt;
    /// let v: Vec<&str> = "Mary had a little lambda".splitter(' ').with_limit(3).collect();
    /// assert_eq!(v, ["Mary", "had", "a little lambda"]);
    ///
    /// let v: Vec<&str> = "lionXXtigerXleopard".splitter("X").with_limit(3).collect();
    /// assert_eq!(v, ["lion", "", "tigerXleopard"]);
    ///
    /// let v: Vec<&str> = "abcXdef".splitter('X').with_limit(1).collect();
    /// assert_eq!(v, ["abcXdef"]);
    ///
    /// let v: Vec<&str> = "".splitter('X').with_limit(1).collect();
    /// assert_eq!(v, [""]);
    /// ```
    ///
    /// A more complex pattern, using a closure:
    ///
    /// ```
    /// # use str_splitter::combinators::SplitExt;
    /// let v: Vec<&str> = "abc1defXghi".splitter(|c| c == '1' || c == 'X').with_limit(2).collect();
    /// assert_eq!(v, ["abc", "defXghi"]);
    /// ```
    pub fn with_limit(self, n: usize) -> Limited<Self> {
        Limited {
            iter: self,
            count: n,
        }
    }

    #[inline]
    pub fn as_str(&self) -> &'a str {
        self.internal.as_str()
    }
}

impl<'a, P: Pattern<'a>> LimitedInternal<'a> for Splitter<'a, P> {
    fn get_end(&mut self) -> std::option::Option<&'a str> {
        self.internal.get_end()
    }

    fn as_str(&self) -> &'a str {
        self.internal.as_str()
    }
}

pub struct Inclusive<S>(S);

impl<'a, P: Pattern<'a>> Iterator for Inclusive<Splitter<'a, P>> {
    type Item = &'a str;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        self.0.internal.next_inclusive()
    }
}
impl<'a, P: Pattern<'a>> DoubleEndedIterator for Inclusive<Splitter<'a, P>>
where
    P::Searcher: DoubleEndedSearcher<'a>,
{
    #[inline]
    fn next_back(&mut self) -> Option<Self::Item> {
        self.0.internal.next_back_inclusive()
    }
}
impl<S> FusedIterator for Inclusive<S>
where
    Self: Iterator,
    S: FusedIterator,
{
}

impl<'a, P: Pattern<'a>> Inclusive<Splitter<'a, P>> {
    #[inline]
    pub fn once(self) -> Option<(&'a str, &'a str)> {
        self.0.internal.once_inclusive()
    }

    pub fn to_reversed(self) -> Reversed<Inclusive<Splitter<'a, P>>>
    where
        P::Searcher: ReverseSearcher<'a>,
    {
        Reversed(self)
    }

    pub fn with_limit(self, n: usize) -> Limited<Self> {
        Limited {
            iter: self,
            count: n,
        }
    }

    #[inline]
    pub fn as_str(&self) -> &'a str {
        self.0.internal.as_str()
    }
}

impl<'a, S: LimitedInternal<'a>> LimitedInternal<'a> for Inclusive<S> {
    fn get_end(&mut self) -> std::option::Option<&'a str> {
        self.0.get_end()
    }

    fn as_str(&self) -> &'a str {
        self.0.as_str()
    }
}

pub struct Reversed<S>(S);

impl<'a, P> Iterator for Reversed<Splitter<'a, P>>
where
    P: Pattern<'a, Searcher: ReverseSearcher<'a>>,
{
    type Item = &'a str;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        self.0.internal.next_back()
    }
}
impl<'a, P> DoubleEndedIterator for Reversed<Splitter<'a, P>>
where
    P: Pattern<'a, Searcher: DoubleEndedSearcher<'a>>,
{
    #[inline]
    fn next_back(&mut self) -> Option<Self::Item> {
        self.0.internal.next()
    }
}
impl<S> FusedIterator for Reversed<S>
where
    Self: Iterator,
    S: FusedIterator,
{
}

impl<'a, P> Reversed<Splitter<'a, P>>
where
    P: Pattern<'a, Searcher: ReverseSearcher<'a>>,
{
    /// Splits the string on the last occurrence of the specified delimiter and
    /// returns prefix before delimiter and suffix after delimiter.
    ///
    /// # Examples
    ///
    /// ```
    /// # use str_splitter::combinators::SplitExt;
    /// assert_eq!("cfg".splitter('=').to_reversed().once(), None);
    /// assert_eq!("cfg=foo".splitter('=').to_reversed().once(), Some(("cfg", "foo")));
    /// assert_eq!("cfg=foo=bar".splitter('=').to_reversed().once(), Some(("cfg=foo", "bar")));
    /// ```
    #[inline]
    pub fn once(self) -> Option<(&'a str, &'a str)> {
        self.0.internal.once_back()
    }

    /// An iterator over substrings of `self`, separated by characters
    /// matched by a pattern and yielded in reverse order.
    ///
    /// The [pattern] can be a `&str`, [`char`], a slice of [`char`]s, or a
    /// function or closure that determines if a character matches.
    ///
    /// [`char`]: prim@char
    /// [pattern]: self::pattern
    ///
    /// Equivalent to [`split`], except that the trailing substring is
    /// skipped if empty.
    ///
    /// [`split`]: str::split
    ///
    /// This method can be used for string data that is _terminated_,
    /// rather than _separated_ by a pattern.
    ///
    /// # Iterator behavior
    ///
    /// The returned iterator requires that the pattern supports a
    /// reverse search, and it will be double ended if a forward/reverse
    /// search yields the same elements.
    ///
    /// For iterating from the front, the [`split_terminator`] method can be
    /// used.
    ///
    /// [`split_terminator`]: str::split_terminator
    ///
    /// # Examples
    ///
    /// ```
    /// # use str_splitter::combinators::SplitExt;
    /// let v: Vec<&str> = "A.B.".splitter('.').to_terminated().to_reversed().collect();
    /// assert_eq!(v, ["B", "A"]);
    ///
    /// let v: Vec<&str> = "A..B..".splitter(".").to_reversed().to_terminated().collect();
    /// assert_eq!(v, ["", "B", "", "A"]);
    ///
    /// let v: Vec<&str> = "A.B:C.D".splitter(&['.', ':'][..]).to_terminated().to_reversed().collect();
    /// assert_eq!(v, ["D", "C", "B", "A"]);
    /// ```
    pub fn to_terminated(mut self) -> Self {
        self.0.internal.allow_trailing_empty = false;
        self
    }

    /// An iterator over substrings of this string slice, separated by a
    /// pattern, starting from the end of the string, restricted to returning
    /// at most `n` items.
    ///
    /// If `n` substrings are returned, the last substring (the `n`th substring)
    /// will contain the remainder of the string.
    ///
    /// The [pattern] can be a `&str`, [`char`], a slice of [`char`]s, or a
    /// function or closure that determines if a character matches.
    ///
    /// [`char`]: prim@char
    /// [pattern]: self::pattern
    ///
    /// # Iterator behavior
    ///
    /// The returned iterator will not be double ended, because it is not
    /// efficient to support.
    ///
    /// For splitting from the front, the [`splitn`] method can be used.
    ///
    /// [`splitn`]: str::splitn
    ///
    /// # Examples
    ///
    /// Simple patterns:
    ///
    /// ```
    /// # use str_splitter::combinators::SplitExt;
    /// let v: Vec<&str> = "Mary had a little lamb".splitter(' ').to_reversed().with_limit(3).collect();
    /// assert_eq!(v, ["lamb", "little", "Mary had a"]);
    ///
    /// let v: Vec<&str> = "lionXXtigerXleopard".splitter('X').to_reversed().with_limit(3).collect();
    /// assert_eq!(v, ["leopard", "tiger", "lionX"]);
    ///
    /// let v: Vec<&str> = "lion::tiger::leopard".splitter("::").to_reversed().with_limit(2).collect();
    /// assert_eq!(v, ["leopard", "lion::tiger"]);
    /// ```
    ///
    /// A more complex pattern, using a closure:
    ///
    /// ```
    /// # use str_splitter::combinators::SplitExt;
    /// let v: Vec<&str> = "abc1defXghi".splitter(|c| c == '1' || c == 'X').to_reversed().with_limit(2).collect();
    /// assert_eq!(v, ["ghi", "abc1def"]);
    /// ```
    pub fn with_limit(self, n: usize) -> Limited<Self> {
        Limited {
            iter: self,
            count: n,
        }
    }

    #[inline]
    pub fn as_str(&self) -> &'a str {
        self.0.internal.as_str()
    }
}

impl<'a, P> Iterator for Reversed<Inclusive<Splitter<'a, P>>>
where
    P: Pattern<'a, Searcher: ReverseSearcher<'a>>,
{
    type Item = &'a str;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        self.0 .0.internal.next_back_inclusive()
    }
}
impl<'a, P> DoubleEndedIterator for Reversed<Inclusive<Splitter<'a, P>>>
where
    P: Pattern<'a, Searcher: DoubleEndedSearcher<'a>>,
{
    #[inline]
    fn next_back(&mut self) -> Option<Self::Item> {
        self.0 .0.internal.next_inclusive()
    }
}
impl<'a, P> Reversed<Inclusive<Splitter<'a, P>>>
where
    P: Pattern<'a, Searcher: ReverseSearcher<'a>>,
{
    /// Splits the string on the last occurrence of the specified delimiter and
    /// returns prefix before delimiter and suffix including delimiter.
    ///
    /// # Examples
    ///
    /// ```
    /// # use str_splitter::combinators::SplitExt;
    /// assert_eq!("cfg".splitter('=').to_inclusive().to_reversed().once(), None);
    /// assert_eq!("cfg=foo".splitter('=').to_inclusive().to_reversed().once(), Some(("cfg", "=foo")));
    /// assert_eq!("cfg=foo=bar".splitter('=').to_inclusive().to_reversed().once(), Some(("cfg=foo", "=bar")));
    /// ```
    #[inline]
    pub fn once(self) -> Option<(&'a str, &'a str)> {
        self.0 .0.internal.once_back_inclusive()
    }

    pub fn with_limit(self, n: usize) -> Limited<Self> {
        Limited {
            iter: self,
            count: n,
        }
    }

    #[inline]
    pub fn as_str(&self) -> &'a str {
        self.0 .0.internal.as_str()
    }
}

impl<'a, S> LimitedInternal<'a> for Reversed<S>
where
    S: LimitedInternal<'a>,
{
    fn get_end(&mut self) -> std::option::Option<&'a str> {
        self.0.get_end()
    }

    fn as_str(&self) -> &'a str {
        self.0.as_str()
    }
}

// make LimitedInternal inaccessible
mod hidden {
    pub trait LimitedInternal<'a> {
        fn get_end(&mut self) -> Option<&'a str>;
        fn as_str(&self) -> &'a str;
    }
}
use hidden::LimitedInternal;

pub struct Limited<Iter> {
    iter: Iter,
    /// The number of splits remaining
    count: usize,
}

impl<Iter: Clone> Clone for Limited<Iter> {
    fn clone(&self) -> Self {
        Limited {
            iter: self.iter.clone(),
            count: self.count,
        }
    }
}

impl<Iter: fmt::Debug> fmt::Debug for Limited<Iter> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Limited")
            .field("iter", &self.iter)
            .field("count", &self.count)
            .finish()
    }
}

impl<'a, Iter: LimitedInternal<'a>> Limited<Iter> {
    #[inline]
    pub fn as_str(&self) -> &'a str {
        self.iter.as_str()
    }
}

impl<'a, Iter> Iterator for Limited<Iter>
where
    Iter: LimitedInternal<'a> + Iterator<Item = &'a str>,
{
    type Item = &'a str;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        match self.count {
            0 => None,
            1 => {
                self.count = 0;
                self.iter.get_end()
            }
            _ => {
                self.count -= 1;
                self.iter.next()
            }
        }
    }
}
impl<'a, Iter> DoubleEndedIterator for Limited<Iter>
where
    Iter: LimitedInternal<'a> + Iterator<Item = &'a str> + DoubleEndedIterator,
{
    #[inline]
    fn next_back(&mut self) -> Option<Self::Item> {
        match self.count {
            0 => None,
            1 => {
                self.count = 0;
                self.iter.get_end()
            }
            _ => {
                self.count -= 1;
                self.iter.next_back()
            }
        }
    }
}
impl<'a, Iter> FusedIterator for Limited<Iter> where
    Iter: LimitedInternal<'a> + Iterator<Item = &'a str> + FusedIterator
{
}

pub trait SplitExt<'a, P: Pattern<'a>> {
    /// An iterator over substrings of this string slice, separated by
    /// characters matched by a pattern.
    ///
    /// The [pattern] can be a `&str`, [`char`], a slice of [`char`]s, or a
    /// function or closure that determines if a character matches.
    ///
    /// [`char`]: prim@char
    /// [pattern]: self::pattern
    ///
    /// # Iterator behavior
    ///
    /// The returned iterator will be a [`DoubleEndedIterator`] if the pattern
    /// allows a reverse search and forward/reverse search yields the same
    /// elements. This is true for, e.g., [`char`], but not for `&str`.
    ///
    /// If the pattern allows a reverse search but its results might differ
    /// from a forward search, the [`Splitter::to_reversed()`] method can be used.
    ///
    /// # Examples
    ///
    /// Simple patterns:
    ///
    /// ```
    /// # use str_splitter::combinators::SplitExt;
    /// let v: Vec<&str> = "Mary had a little lamb".splitter(' ').collect();
    /// assert_eq!(v, ["Mary", "had", "a", "little", "lamb"]);
    ///
    /// let v: Vec<&str> = "".splitter('X').collect();
    /// assert_eq!(v, [""]);
    ///
    /// let v: Vec<&str> = "lionXXtigerXleopard".splitter('X').collect();
    /// assert_eq!(v, ["lion", "", "tiger", "leopard"]);
    ///
    /// let v: Vec<&str> = "lion::tiger::leopard".splitter("::").collect();
    /// assert_eq!(v, ["lion", "tiger", "leopard"]);
    ///
    /// let v: Vec<&str> = "abc1def2ghi".splitter(char::is_numeric).collect();
    /// assert_eq!(v, ["abc", "def", "ghi"]);
    ///
    /// let v: Vec<&str> = "lionXtigerXleopard".splitter(char::is_uppercase).collect();
    /// assert_eq!(v, ["lion", "tiger", "leopard"]);
    /// ```
    ///
    /// If the pattern is a slice of chars, split on each occurrence of any of the characters:
    ///
    /// ```
    /// # use str_splitter::combinators::SplitExt;
    /// let v: Vec<&str> = "2020-11-03 23:59".splitter(&['-', ' ', ':', '@'][..]).collect();
    /// assert_eq!(v, ["2020", "11", "03", "23", "59"]);
    /// ```
    ///
    /// A more complex pattern, using a closure:
    ///
    /// ```
    /// # use str_splitter::combinators::SplitExt;
    /// let v: Vec<&str> = "abc1defXghi".splitter(|c| c == '1' || c == 'X').collect();
    /// assert_eq!(v, ["abc", "def", "ghi"]);
    /// ```
    ///
    /// If a string contains multiple contiguous separators, you will end up
    /// with empty strings in the output:
    ///
    /// ```
    /// # use str_splitter::combinators::SplitExt;
    /// let x = "||||a||b|c".to_string();
    /// let d: Vec<_> = x.splitter('|').collect();
    ///
    /// assert_eq!(d, &["", "", "", "", "a", "", "b", "c"]);
    /// ```
    ///
    /// Contiguous separators are separated by the empty string.
    ///
    /// ```
    /// # use str_splitter::combinators::SplitExt;
    /// let x = "(///)".to_string();
    /// let d: Vec<_> = x.splitter('/').collect();
    ///
    /// assert_eq!(d, &["(", "", "", ")"]);
    /// ```
    ///
    /// Separators at the start or end of a string are neighbored
    /// by empty strings.
    ///
    /// ```
    /// # use str_splitter::combinators::SplitExt;
    /// let d: Vec<_> = "010".splitter("0").collect();
    /// assert_eq!(d, &["", "1", ""]);
    /// ```
    ///
    /// When the empty string is used as a separator, it separates
    /// every character in the string, along with the beginning
    /// and end of the string.
    ///
    /// ```
    /// # use str_splitter::combinators::SplitExt;
    /// let f: Vec<_> = "rust".splitter("").collect();
    /// assert_eq!(f, &["", "r", "u", "s", "t", ""]);
    /// ```
    ///
    /// Contiguous separators can lead to possibly surprising behavior
    /// when whitespace is used as the separator. This code is correct:
    ///
    /// ```
    /// # use str_splitter::combinators::SplitExt;
    /// let x = "    a  b c".to_string();
    /// let d: Vec<_> = x.splitter(' ').collect();
    ///
    /// assert_eq!(d, &["", "", "", "", "a", "", "b", "c"]);
    /// ```
    ///
    /// It does _not_ give you:
    ///
    /// ```,ignore
    /// assert_eq!(d, &["a", "b", "c"]);
    /// ```
    ///
    /// Use [`split_whitespace`] for this behavior.
    ///
    /// [`split_whitespace`]: str::split_whitespace
    fn splitter(&'a self, pat: P) -> Splitter<'a, P>;
}
impl<'a, P: Pattern<'a>> SplitExt<'a, P> for str {
    fn splitter(&'a self, pat: P) -> Splitter<'a, P> {
        Splitter {
            internal: SplitInternal {
                start: 0,
                end: self.len(),
                matcher: pat.into_searcher(self),
                allow_trailing_empty: true,
                finished: false,
            },
        }
    }
}

#[allow(dead_code)]
#[test]
fn should_impl_traits() {
    use SplitExt;

    fn forward(input: &str) -> impl Iterator<Item = &str> + FusedIterator + DoubleEndedIterator {
        input.splitter('a')
    }

    fn forward_inclusive(
        input: &str,
    ) -> impl Iterator<Item = &str> + FusedIterator + DoubleEndedIterator {
        input.splitter('a').to_inclusive()
    }

    fn reverse(input: &str) -> impl Iterator<Item = &str> + FusedIterator + DoubleEndedIterator {
        input.splitter('a').to_reversed()
    }

    fn reverse_inclusive(
        input: &str,
    ) -> impl Iterator<Item = &str> + FusedIterator + DoubleEndedIterator {
        input.splitter('a').to_inclusive().to_reversed()
    }

    fn reverse_inclusiven(
        input: &str,
    ) -> impl Iterator<Item = &str> + FusedIterator + DoubleEndedIterator {
        input
            .splitter('a')
            .to_inclusive()
            .to_reversed()
            .with_limit(4)
    }
}

// addition to `SplitInternal` for `split_once` functionality
impl<'a, P: Pattern<'a>> SplitInternal<'a, P> {
    fn once(mut self) -> Option<(&'a str, &'a str)> {
        if self.finished {
            return None;
        }

        let haystack = self.matcher.haystack();
        let (start, end) = self.matcher.next_match()?;
        // SAFETY:
        // `Searcher` is known to return valid indices.
        // `self.start` and `self.end` always lie on unicode boundaries.
        unsafe {
            Some((
                haystack.get_unchecked(self.start..start),
                haystack.get_unchecked(end..self.end),
            ))
        }
    }

    fn once_back(mut self) -> Option<(&'a str, &'a str)>
    where
        P::Searcher: ReverseSearcher<'a>,
    {
        if self.finished {
            return None;
        }

        let haystack = self.matcher.haystack();
        let (start, end) = self.matcher.next_match_back()?;
        // SAFETY:
        // `Searcher` is known to return valid indices.
        // `self.start` and `self.end` always lie on unicode boundaries.
        unsafe {
            Some((
                haystack.get_unchecked(self.start..start),
                haystack.get_unchecked(end..self.end),
            ))
        }
    }

    fn once_inclusive(mut self) -> Option<(&'a str, &'a str)> {
        if self.finished {
            return None;
        }

        let haystack = self.matcher.haystack();
        let (_, end) = self.matcher.next_match()?;
        // SAFETY:
        // `Searcher` is known to return valid indices.
        // `self.start` and `self.end` always lie on unicode boundaries.
        unsafe {
            Some((
                haystack.get_unchecked(self.start..end),
                haystack.get_unchecked(end..self.end),
            ))
        }
    }

    fn once_back_inclusive(mut self) -> Option<(&'a str, &'a str)>
    where
        P::Searcher: ReverseSearcher<'a>,
    {
        if self.finished {
            return None;
        }

        let haystack = self.matcher.haystack();
        let (start, _) = self.matcher.next_match_back()?;
        // SAFETY:
        // `Searcher` is known to return valid indices.
        // `self.start` and `self.end` always lie on unicode boundaries.
        unsafe {
            Some((
                haystack.get_unchecked(self.start..start),
                haystack.get_unchecked(start..self.end),
            ))
        }
    }
}

// ========================================
// from core/str/iter.rs
// ========================================

impl<'a, P> Clone for SplitInternal<'a, P>
where
    P: Pattern<'a, Searcher: Clone>,
{
    fn clone(&self) -> Self {
        SplitInternal {
            matcher: self.matcher.clone(),
            ..*self
        }
    }
}

/* pub(super) */
struct SplitInternal<'a, P: Pattern<'a>> {
    /* pub(super) */ start: usize,
    /* pub(super) */ end: usize,
    /* pub(super) */ matcher: P::Searcher,
    /* pub(super) */ allow_trailing_empty: bool,
    /* pub(super) */ finished: bool,
}

impl<'a, P> fmt::Debug for SplitInternal<'a, P>
where
    P: Pattern<'a, Searcher: fmt::Debug>,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("SplitInternal")
            .field("start", &self.start)
            .field("end", &self.end)
            .field("matcher", &self.matcher)
            .field("allow_trailing_empty", &self.allow_trailing_empty)
            .field("finished", &self.finished)
            .finish()
    }
}

impl<'a, P: Pattern<'a>> SplitInternal<'a, P> {
    #[inline]
    fn get_end(&mut self) -> Option<&'a str> {
        if !self.finished && (self.allow_trailing_empty || self.end - self.start > 0) {
            self.finished = true;
            // SAFETY: `self.start` and `self.end` always lie on unicode boundaries.
            unsafe {
                let string = self.matcher.haystack().get_unchecked(self.start..self.end);
                Some(string)
            }
        } else {
            None
        }
    }

    #[inline]
    fn next(&mut self) -> Option<&'a str> {
        if self.finished {
            return None;
        }

        let haystack = self.matcher.haystack();
        match self.matcher.next_match() {
            // SAFETY: `Searcher` guarantees that `a` and `b` lie on unicode boundaries.
            Some((a, b)) => unsafe {
                let elt = haystack.get_unchecked(self.start..a);
                self.start = b;
                Some(elt)
            },
            None => self.get_end(),
        }
    }

    #[inline]
    fn next_inclusive(&mut self) -> Option<&'a str> {
        if self.finished {
            return None;
        }

        let haystack = self.matcher.haystack();
        match self.matcher.next_match() {
            // SAFETY: `Searcher` guarantees that `b` lies on unicode boundary,
            // and self.start is either the start of the original string,
            // or `b` was assigned to it, so it also lies on unicode boundary.
            Some((_, b)) => unsafe {
                let elt = haystack.get_unchecked(self.start..b);
                self.start = b;
                Some(elt)
            },
            None => self.get_end(),
        }
    }

    #[inline]
    fn next_back(&mut self) -> Option<&'a str>
    where
        P::Searcher: ReverseSearcher<'a>,
    {
        if self.finished {
            return None;
        }

        if !self.allow_trailing_empty {
            self.allow_trailing_empty = true;
            match self.next_back() {
                Some(elt) if !elt.is_empty() => return Some(elt),
                _ => {
                    if self.finished {
                        return None;
                    }
                }
            }
        }

        let haystack = self.matcher.haystack();
        match self.matcher.next_match_back() {
            // SAFETY: `Searcher` guarantees that `a` and `b` lie on unicode boundaries.
            Some((a, b)) => unsafe {
                let elt = haystack.get_unchecked(b..self.end);
                self.end = a;
                Some(elt)
            },
            // SAFETY: `self.start` and `self.end` always lie on unicode boundaries.
            None => unsafe {
                self.finished = true;
                Some(haystack.get_unchecked(self.start..self.end))
            },
        }
    }

    #[inline]
    fn next_back_inclusive(&mut self) -> Option<&'a str>
    where
        P::Searcher: ReverseSearcher<'a>,
    {
        if self.finished {
            return None;
        }

        if !self.allow_trailing_empty {
            self.allow_trailing_empty = true;
            match self.next_back_inclusive() {
                Some(elt) if !elt.is_empty() => return Some(elt),
                _ => {
                    if self.finished {
                        return None;
                    }
                }
            }
        }

        let haystack = self.matcher.haystack();
        match self.matcher.next_match_back() {
            // SAFETY: `Searcher` guarantees that `b` lies on unicode boundary,
            // and self.end is either the end of the original string,
            // or `b` was assigned to it, so it also lies on unicode boundary.
            Some((_, b)) => unsafe {
                let elt = haystack.get_unchecked(b..self.end);
                self.end = b;
                Some(elt)
            },
            // SAFETY: self.start is either the start of the original string,
            // or start of a substring that represents the part of the string that hasn't
            // iterated yet. Either way, it is guaranteed to lie on unicode boundary.
            // self.end is either the end of the original string,
            // or `b` was assigned to it, so it also lies on unicode boundary.
            None => unsafe {
                self.finished = true;
                Some(haystack.get_unchecked(self.start..self.end))
            },
        }
    }

    #[inline]
    fn as_str(&self) -> &'a str {
        // `Self::get_end` doesn't change `self.start`
        if self.finished {
            return "";
        }

        // SAFETY: `self.start` and `self.end` always lie on unicode boundaries.
        unsafe { self.matcher.haystack().get_unchecked(self.start..self.end) }
    }
}
