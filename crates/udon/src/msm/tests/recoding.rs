use super::*;

#[derive(Debug, PartialEq, Eq)]
enum RowEvent {
    Slice(usize, usize),
    Contiguous(usize, usize),
    Get(usize),
    Visit(usize, i16, i16),
}

#[derive(Clone, Copy)]
struct ObservedRows<'a> {
    data: &'a [u8],
    start: usize,
    end: usize,
    mask: u8,
    queries: &'a core::cell::Cell<usize>,
    events: &'a core::cell::RefCell<Vec<RowEvent>>,
    short_second: bool,
    panic_second_query: bool,
}

impl super::super::storage::Storage<u8> for ObservedRows<'_> {
    fn len(self) -> usize {
        self.end - self.start
    }

    fn get(self, index: usize) -> u8 {
        self.events
            .borrow_mut()
            .push(RowEvent::Get(self.start + index));
        assert!(index < self.end - self.start);
        self.data[self.start + index]
    }

    fn slice(self, range: core::ops::Range<usize>) -> Self {
        assert!(range.start <= range.end && range.end <= self.end - self.start);
        let start = self.start + range.start;
        let end = self.start + range.end;
        self.events.borrow_mut().push(RowEvent::Slice(start, end));
        Self { start, end, ..self }
    }

    fn contiguous(&self) -> Option<&[u8]> {
        let query = self.queries.get();
        self.queries.set(query + 1);
        self.events
            .borrow_mut()
            .push(RowEvent::Contiguous(self.start, self.end));
        assert!(
            !self.panic_second_query || query != 1,
            "second row provider panic"
        );
        if self.mask & (1 << (query % 2)) == 0 {
            None
        } else if self.short_second && query == 1 {
            Some(&self.data[self.start..self.start])
        } else {
            Some(&self.data[self.start..self.end])
        }
    }
}

fn signed_row_value(term: usize, half: usize, window: usize, bytes: usize) -> i16 {
    let i = (term + half * 2 + window) % 7;
    if bytes == 1 {
        [0, 1, 127, -128, -1, 42, -2][i]
    } else {
        [0, 1, 32767, -32768, -1, 256, -257][i]
    }
}

// Build the format by appending complete rows, recording each logical value's
// location. Expectations below do not call rows/rows_view or the cache writer.
fn observed_row_fixture(
    terms: usize,
    geometry: recode::Geometry,
) -> (Vec<u8>, Vec<Vec<[usize; 2]>>) {
    let bytes = if geometry.width() <= 8 { 1 } else { 2 };
    let mut data = vec![0xa5; 3];
    let mut locations = vec![vec![[0; 2]; terms]; geometry.windows()];
    for start in (0..terms).step_by(recode::CHUNK) {
        let end = terms.min(start + recode::CHUNK);
        for (window, window_locations) in locations.iter_mut().enumerate() {
            for half in 0..2 {
                for (offset, slots) in window_locations[start..end].iter_mut().enumerate() {
                    slots[half] = data.len();
                    let value = signed_row_value(start + offset, half, window, bytes).to_le_bytes();
                    data.extend_from_slice(&value[..bytes]);
                }
            }
        }
    }
    data.extend_from_slice(&[0x5a; 3]);
    (data, locations)
}

#[test]
fn production_rows_view_preserves_provider_and_visit_order() {
    use core::cell::{Cell, RefCell};
    let terms = 353;
    for width in 4..=12 {
        let geometry = recode::Geometry::Booth(width);
        let bytes = if width <= 8 { 1 } else { 2 };
        let (data, locations) = observed_row_fixture(terms, geometry);
        let snapshot = data.clone();
        for window in [0, geometry.windows() - 1] {
            for range in [0..0, 7..19, 255..258, 256..353, 352..353, 353..353] {
                for mask in 0..4 {
                    let queries = Cell::new(0);
                    let events = RefCell::new(Vec::new());
                    let rows = ObservedRows {
                        data: &data,
                        start: 3,
                        end: data.len() - 3,
                        mask,
                        queries: &queries,
                        events: &events,
                        short_second: false,
                        panic_second_query: false,
                    };
                    recode::rows_view(
                        rows,
                        terms,
                        range.clone(),
                        geometry,
                        window,
                        |term, a, b| {
                            events.borrow_mut().push(RowEvent::Visit(term, a, b));
                        },
                    );
                    let mut expected = Vec::new();
                    for start in (0..terms).step_by(recode::CHUNK) {
                        let end = terms.min(start + recode::CHUNK);
                        let first = range.start.max(start);
                        let last = range.end.min(end);
                        if first >= last {
                            continue;
                        }
                        let a = locations[window][start][0];
                        let b = locations[window][start][1];
                        let len = (end - start) * bytes;
                        expected.extend([
                            RowEvent::Slice(a, a + len),
                            RowEvent::Slice(b, b + len),
                            RowEvent::Contiguous(a, a + len),
                            RowEvent::Contiguous(b, b + len),
                        ]);
                        for (offset, slots) in locations[window][first..last].iter().enumerate() {
                            let term = first + offset;
                            for (half, location) in slots.iter().enumerate() {
                                if mask & (1 << half) == 0 {
                                    for byte in 0..bytes {
                                        expected.push(RowEvent::Get(location + byte));
                                    }
                                }
                            }
                            expected.push(RowEvent::Visit(
                                term,
                                signed_row_value(term, 0, window, bytes),
                                signed_row_value(term, 1, window, bytes),
                            ));
                        }
                    }
                    assert_eq!(
                        *events.borrow(),
                        expected,
                        "width={width}, mask={mask}, range={range:?}, window={window}"
                    );
                    assert_eq!(
                        queries.get(),
                        expected
                            .iter()
                            .filter(|event| matches!(event, RowEvent::Contiguous(..)))
                            .count()
                    );
                    assert_eq!(data, snapshot);
                }
            }
        }
    }
}

#[test]
fn production_rows_view_stops_at_callback_and_provider_panics() {
    use core::cell::{Cell, RefCell};
    use std::panic::{AssertUnwindSafe, catch_unwind};
    for width in [8, 9] {
        let geometry = recode::Geometry::Booth(width);
        let bytes = if width <= 8 { 1 } else { 2 };
        let (data, locations) = observed_row_fixture(353, geometry);
        for mask in 0..4 {
            for provider_panic in [false, true] {
                let queries = Cell::new(0);
                let events = RefCell::new(Vec::new());
                let rows = ObservedRows {
                    data: &data,
                    start: 3,
                    end: data.len() - 3,
                    mask,
                    queries: &queries,
                    events: &events,
                    short_second: false,
                    panic_second_query: provider_panic,
                };
                let result = catch_unwind(AssertUnwindSafe(|| {
                    recode::rows_view(rows, 353, 255..258, geometry, 0, |term, a, b| {
                        events.borrow_mut().push(RowEvent::Visit(term, a, b));
                        panic!("visitor stops before next chunk");
                    });
                }));
                assert!(result.is_err());
                let a = locations[0][0][0];
                let b = locations[0][0][1];
                let len = recode::CHUNK * bytes;
                let mut expected = vec![
                    RowEvent::Slice(a, a + len),
                    RowEvent::Slice(b, b + len),
                    RowEvent::Contiguous(a, a + len),
                    RowEvent::Contiguous(b, b + len),
                ];
                if !provider_panic {
                    for (half, location) in locations[0][255].iter().enumerate() {
                        if mask & (1 << half) == 0 {
                            for byte in 0..bytes {
                                expected.push(RowEvent::Get(location + byte));
                            }
                        }
                    }
                    expected.push(RowEvent::Visit(
                        255,
                        signed_row_value(255, 0, 0, bytes),
                        signed_row_value(255, 1, 0, bytes),
                    ));
                }
                assert_eq!(*events.borrow(), expected);
                assert_eq!(queries.get(), 2);
            }
        }
    }
}

#[test]
fn production_rows_view_checks_both_slices_before_queries_and_some_bounds_before_visit() {
    use core::cell::{Cell, RefCell};
    use std::panic::{AssertUnwindSafe, catch_unwind};
    let geometry = recode::Geometry::Booth(8);
    let (data, locations) = observed_row_fixture(353, geometry);
    for short_second in [false, true] {
        let queries = Cell::new(0);
        let events = RefCell::new(Vec::new());
        let rows = ObservedRows {
            data: &data,
            start: 3,
            end: if short_second {
                data.len() - 3
            } else {
                locations[0][0][1]
            },
            mask: 3,
            queries: &queries,
            events: &events,
            short_second,
            panic_second_query: false,
        };
        let result = catch_unwind(AssertUnwindSafe(|| {
            recode::rows_view(rows, 353, 7..8, geometry, 0, |term, a, b| {
                events.borrow_mut().push(RowEvent::Visit(term, a, b));
            });
        }));
        assert!(result.is_err());
        let a = locations[0][0][0];
        let b = locations[0][0][1];
        let mut expected = vec![RowEvent::Slice(a, a + recode::CHUNK)];
        if short_second {
            expected.extend([
                RowEvent::Slice(b, b + recode::CHUNK),
                RowEvent::Contiguous(a, a + recode::CHUNK),
                RowEvent::Contiguous(b, b + recode::CHUNK),
            ]);
        }
        assert_eq!(*events.borrow(), expected);
        assert_eq!(queries.get(), if short_second { 2 } else { 0 });
    }
}

#[test]
fn production_booth_rows_reconstruct_both_glv_halves() {
    fn check<C: PastaCurve>() {
        use num_bigint::BigInt;
        for tail in 1..=recode::CHUNK {
            let n = recode::CHUNK + tail;
            let scalars: Vec<_> = field_samples::<C::Scalar>().take(n).collect();
            let mut storage = vec![ScalarStorage::<C>::ZERO; n];
            let retained = PreparedScalars::prepare(
                &scalars,
                &mut storage,
                TaskBudget::SERIAL,
                &SerialExecutor,
            );
            for width in 4..=12 {
                let geometry = recode::Geometry::Booth(width);
                let mut digits = vec![73; geometry.storage_len(n).unwrap()];
                recode::write(retained.records, geometry, &mut digits);
                let mut values = vec![[BigInt::from(0), BigInt::from(0)]; n];
                for window in (0..geometry.windows()).rev() {
                    recode::rows(&digits, n, 0..n, geometry, window, |term, a, b| {
                        values[term][0] = (&values[term][0] << width) + BigInt::from(a);
                        values[term][1] = (&values[term][1] << width) + BigInt::from(b);
                    });
                }
                for (term, record) in retained.records.iter().enumerate() {
                    assert_eq!(values[term], record.halves.map(BigInt::from));
                }
            }
        }
    }
    check::<Pallas>();
    check::<Vesta>();
}

#[test]
fn production_booth_bounds_and_partial_row_visits() {
    fn check<C: PastaCurve>() {
        use crate::curve::pasta::parameters::GlvParameters;
        use num_bigint::BigInt;
        let mut records = vec![ScalarStorage::<C>::ZERO; 2049];
        for (i, record) in records.iter_mut().enumerate() {
            for (half, bound) in GlvParameters::<C>::BOUNDS.into_iter().enumerate() {
                let magnitude = match i % 6 {
                    0 => bound,
                    1 => bound - 1,
                    2 => 0,
                    3 => 1,
                    4 => 128,
                    _ => 255,
                };
                record.halves[half] = if (i / 6 + half) % 2 == 0 {
                    magnitude as i128
                } else {
                    -(magnitude as i128)
                };
            }
        }
        for width in 4..=12 {
            let geometry = recode::Geometry::Booth(width);
            let mut digits = vec![73; geometry.storage_len(records.len()).unwrap() + 1];
            recode::write_parallel(
                &records,
                geometry,
                &mut digits[..geometry.storage_len(records.len()).unwrap()],
                None,
                TaskBudget::new(7).unwrap(),
                &Pool,
            );
            assert_eq!(*digits.last().unwrap(), 73);
            for range in [0..2049, 1..255, 255..257, 256..513, 511..2049, 2049..2049] {
                // The midpoint conventions can yield different digit sequences;
                // reconstruct integers to compare their mathematical meaning.
                for direct in [false, true] {
                    let mut values = vec![[BigInt::from(0), BigInt::from(0)]; records.len()];
                    let mut visits = vec![0; records.len()];
                    for window in (0..geometry.windows()).rev() {
                        let visit = |i: usize, a: i16, b: i16| {
                            visits[i] += 1;
                            values[i][0] = (&values[i][0] << width) + a;
                            values[i][1] = (&values[i][1] << width) + b;
                        };
                        if direct {
                            recode::window_rows::<C, true>(
                                &records,
                                &[],
                                range.clone(),
                                geometry,
                                window,
                                visit,
                            );
                        } else {
                            recode::rows(
                                &digits,
                                records.len(),
                                range.clone(),
                                geometry,
                                window,
                                visit,
                            );
                        }
                    }
                    for (i, record) in records.iter().enumerate() {
                        assert_eq!(
                            visits[i],
                            if range.contains(&i) {
                                geometry.windows()
                            } else {
                                0
                            }
                        );
                        assert_eq!(
                            values[i],
                            if range.contains(&i) {
                                record.halves.map(BigInt::from)
                            } else {
                                [BigInt::from(0), BigInt::from(0)]
                            }
                        );
                    }
                }
            }
        }
    }
    check::<Pallas>();
    check::<Vesta>();
}
