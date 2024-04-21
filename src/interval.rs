use std::cmp::{max, min, Ordering};
use std::ops::{Add, Deref, Div, Mul, Sub};
use crate::interval::Bound;


#[derive(Debug, Clone)]
pub struct Interval<T> {
    start: Bound<T>,
    end: Bound<T>,
}

impl<T> Interval<T> {
    pub fn open(start: T, end: T) -> Self {
        Self { start: Bound::Exclusive(start), end: Bound::Exclusive(end) }
    }

    pub fn closed(start: T, end: T) -> Self {
        Self { start: Bound::LeftInclusive(start), end: Bound::RightInclusive(end) }
    }

    pub fn left_closed(start: T, end: T) -> Self {
        Self { start: Bound::LeftInclusive(start), end: Bound::Exclusive(end) }
    }

    pub fn right_closed(start: T, end: T) -> Self {
        Self { start: Bound::Exclusive(start), end: Bound::RightInclusive(end) }
    }

    pub fn start(&self) -> &Bound<T> {
        &self.start
    }

    pub fn end(&self) -> &Bound<T> {
        &self.end
    }
}

impl<T> PartialEq for Interval<T>
    where T: Eq
{
    fn eq(&self, other: &Self) -> bool {
        self.start == other.start && self.end == other.end
    }
}

impl<T> Eq for Interval<T> where T: Eq {}

impl<T> PartialOrd for Interval<T>
    where T: Ord
{
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        if self.start != other.start {
            Some(self.start.cmp(&other.start))
        } else {
            Some(self.end.cmp(&other.end))
        }
    }
}

impl<T> Ord for Interval<T>
    where T: Ord
{
    fn cmp(&self, other: &Self) -> Ordering {
        self.partial_cmp(other).unwrap()
    }
}

#[derive(Debug, PartialEq, Eq)]
pub enum OverlapType {
    /// [self] [other]
    Left,
    /// [other] [self]
    Right,
    ///  [self]
    ///[  other  ]
    Inside,
    ///[  self  ]
    ///  [other]
    Outside,
    ///[  self  ]
    ///  [  other  ]
    Before,
    ///  [  self   ]
    ///[  other  ]
    After,
}


impl<T> Interval<T> where T: Ord {
    pub fn union(self, other: Interval<T>) -> Vec<Interval<T>> {
        match self.overlap(&other) {
            OverlapType::Left => vec![self, other],
            OverlapType::Right => vec![other, self],
            _ => vec![Interval {
                start: min(self.start, other.start),
                end: max(self.end, other.end),
            }],
        }
    }

    pub fn intersect(self, other: Interval<T>) -> Vec<Interval<T>> {
        match self.overlap(&other) {
            OverlapType::Left => vec![self, other],
            OverlapType::Right => vec![other, self],
            _ => vec![Interval {
                start: max(self.start, other.start),
                end: min(self.end, other.end),
            }],
        }
    }

    pub fn diff(self, other: Interval<T>) -> Vec<Interval<T>> {
        match self.overlap(&other) {
            OverlapType::Left => vec![self, other],
            OverlapType::Right => vec![other, self],
            _ => {
                let first = match self.start.cmp(&other.start) {
                    // todo: handle bound
                    Ordering::Less => Interval { start: self.start, end: other.start.to_right() },
                    _ => Interval { start: other.start, end: self.start.to_right() }
                };
                let second = match self.end.cmp(&other.end) {
                    // todo: handle bound
                    Ordering::Less => Interval { start: self.end.to_left(), end: other.end },
                    _ => Interval { start: other.end.to_left(), end: self.end }
                };

                vec![first, second]
            }
        }
    }

    pub fn overlap(&self, other: &Interval<T>) -> OverlapType {
        // [---self---]
        //            [---other---]
        if self.end <= other.start || other.end <= self.start {
            OverlapType::Left
        }
        //    [---self---]
        // [-------other--------]
        else if self.start >= other.start && self.end <= other.end {
            OverlapType::Inside
        }
        // [-------self--------]
        //    [---other---]
        else if self.start <= other.start && self.end >= other.end {
            OverlapType::Outside
        }
        // [---self---]
        //    [---other---]
        else if self.end <= other.end {
            OverlapType::Before
        }
        //      [---self---]
        // [---other---]
        else {
            OverlapType::After
        }
    }

    pub fn overlap_point(&self, point: &T) -> Ordering {
        // if point is left to the start so interval is greater than the point
        if let Bound::LeftInclusive(t) = &self.start {
            if point < t {
                return Ordering::Greater;
            }
        } else if let Bound::Exclusive(t) = &self.start {
            if point <= t {
                return Ordering::Greater;
            }
        }

        // if point is right to the end so interval is less than the point
        if let Bound::RightInclusive(t) = &self.end {
            if point > t {
                return Ordering::Less;
            }
        } else if let Bound::Exclusive(t) = &self.end {
            if point >= t {
                return Ordering::Less;
            }
        }

        // the point overlap the interval
        return Ordering::Equal;
    }
}

fn process_intervals<T: Ord, F>(
    intervals: Vec<Interval<T>>,
    operation: F,
) -> Vec<Interval<T>>
    where
        F: Fn(Interval<T>, Interval<T>) -> Vec<Interval<T>>,
{
    intervals
        .into_iter()
        .fold(Vec::new(), |mut acc, next| {
            if let Some(prev) = acc.pop() {
                let mut vec1 = operation(prev, next);
                acc.append(&mut vec1);
                acc
            } else {
                acc.push(next);
                acc
            }
        })
}

pub fn intersect_intervals<T: Ord>(intervals: Vec<Interval<T>>) -> Vec<Interval<T>> {
    process_intervals(intervals, Interval::intersect)
}

pub fn union_intervals<T: Ord>(intervals: Vec<Interval<T>>) -> Vec<Interval<T>> {
    process_intervals(intervals, Interval::union)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_bound_deref() {
        let left = Bound::LeftInclusive(5);
        assert_eq!(*left, 5);

        let right = Bound::RightInclusive(10);
        assert_eq!(*right, 10);

        let exclusive = Bound::Exclusive(15);
        assert_eq!(*exclusive, 15);
    }

    #[test]
    fn test_bound_eq() {
        let left1 = Bound::LeftInclusive(5);
        let left2 = Bound::LeftInclusive(5);
        assert_eq!(left1, left2);

        let right1 = Bound::RightInclusive(10);
        let right2 = Bound::RightInclusive(10);
        assert_eq!(right1, right2);

        let exclusive1 = Bound::Exclusive(15);
        let exclusive2 = Bound::Exclusive(15);
        assert_eq!(exclusive1, exclusive2);

        assert_ne!(left1, right1);
        assert_ne!(left1, exclusive1);
        assert_ne!(right1, exclusive1);
    }

    #[test]
    fn test_bound_partial_cmp_left() {
        let left1 = Bound::LeftInclusive(5);
        let left2 = Bound::LeftInclusive(10);
        assert_eq!(left1.partial_cmp(&left2), Some(Ordering::Less));
    }

    #[test]
    fn test_bound_partial_cmp_right() {
        let right1 = Bound::RightInclusive(15);
        let right2 = Bound::RightInclusive(10);
        assert_eq!(right1.partial_cmp(&right2), Some(Ordering::Greater));
    }

    #[test]
    fn test_bound_partial_cmp_exclusive() {
        let exclusive1 = Bound::Exclusive(20);
        let exclusive2 = Bound::Exclusive(20);
        assert_eq!(exclusive1.partial_cmp(&exclusive2), Some(Ordering::Equal));
    }

    #[test]
    fn test_bound_partial_cmp_left_and_right() {
        let left1 = Bound::LeftInclusive(5);
        let right1 = Bound::RightInclusive(15);
        assert_eq!(left1.partial_cmp(&right1), Some(Ordering::Less));
    }

    #[test]
    fn test_bound_partial_cmp_left_and_exclusive() {
        let left1 = Bound::LeftInclusive(5);
        let exclusive1 = Bound::Exclusive(20);

        assert_eq!(left1.partial_cmp(&exclusive1), Some(Ordering::Less));
    }

    #[test]
    fn test_bound_partial_cmp_right_and_exclusive() {
        let right1 = Bound::RightInclusive(15);
        let exclusive1 = Bound::Exclusive(15);

        assert_eq!(right1.partial_cmp(&exclusive1), Some(Ordering::Greater));
    }

    #[test]
    fn test_interval_constructors() {
        let open_interval = Interval::open(1, 5);
        assert_eq!(open_interval.start, Bound::Exclusive(1));
        assert_eq!(open_interval.end, Bound::Exclusive(5));

        let closed_interval = Interval::closed(1, 5);
        assert_eq!(closed_interval.start, Bound::LeftInclusive(1));
        assert_eq!(closed_interval.end, Bound::RightInclusive(5));

        let left_closed_interval = Interval::left_closed(1, 5);
        assert_eq!(left_closed_interval.start, Bound::LeftInclusive(1));
        assert_eq!(left_closed_interval.end, Bound::Exclusive(5));

        let right_closed_interval = Interval::right_closed(1, 5);
        assert_eq!(right_closed_interval.start, Bound::Exclusive(1));
        assert_eq!(right_closed_interval.end, Bound::RightInclusive(5));
    }

    #[test]
    fn test_interval_eq() {
        let interval1 = Interval::closed(1, 5);
        let interval2 = Interval::closed(1, 5);
        assert_eq!(interval1, interval2);

        let interval3 = Interval::open(1, 5);
        assert_ne!(interval1, interval3);

        let interval4 = Interval::closed(2, 5);
        assert_ne!(interval1, interval4);
    }

    #[test]
    fn test_interval_partial_cmp() {
        let interval1 = Interval::closed(1, 5);
        let interval2 = Interval::closed(1, 5);
        assert_eq!(interval1.partial_cmp(&interval2), Some(Ordering::Equal));

        let interval3 = Interval::open(1, 5);
        assert_eq!(interval1.partial_cmp(&interval3), Some(Ordering::Less));

        let interval4 = Interval::closed(2, 5);
        assert_eq!(interval1.partial_cmp(&interval4), Some(Ordering::Less));

        let interval5 = Interval::closed(1, 6);
        assert_eq!(interval1.partial_cmp(&interval5), Some(Ordering::Less));
    }

    #[test]
    fn test_interval_overlap_no_overlap() {
        let interval1 = Interval::closed(1, 5);
        let interval2 = Interval::closed(6, 10);
        assert_eq!(interval1.overlap(&interval2), OverlapType::Left);
    }

    #[test]
    fn test_interval_overlap_inside() {
        let interval1 = Interval::closed(1, 5);
        let interval3 = Interval::closed(0, 7);
        assert_eq!(interval1.overlap(&interval3), OverlapType::Inside);
    }

    #[test]
    fn test_interval_overlap_outside() {
        let interval1 = Interval::closed(1, 5);
        let interval4 = Interval::closed(2, 3);
        assert_eq!(interval1.overlap(&interval4), OverlapType::Outside);
    }

    #[test]
    fn test_interval_overlap_after() {
        let interval1 = Interval::closed(1, 5);
        let interval5 = Interval::closed(0, 3);
        assert_eq!(interval1.overlap(&interval5), OverlapType::After);
    }

    #[test]
    fn test_interval_overlap_before() {
        let interval1 = Interval::closed(1, 5);
        let interval6 = Interval::closed(4, 7);
        assert_eq!(interval1.overlap(&interval6), OverlapType::Before);
    }

    #[test]
    fn test_interval_union() {
        let interval1 = Interval::closed(1, 5);
        let interval2 = Interval::closed(3, 7);
        let result = interval1.clone().union(interval2);
        assert_eq!(result.len(), 1);
        assert_eq!(result[0], Interval::closed(1, 7));

        let interval3 = Interval::closed(10, 15);
        let result = interval1.clone().union(interval3.clone());
        assert_eq!(result.len(), 2);
        assert_eq!(result[0], interval1);
        assert_eq!(result[1], interval3);
    }

    #[test]
    fn test_interval_intersect() {
        let interval1 = Interval::closed(1, 5);
        let interval2 = Interval::closed(3, 7);
        let result = interval1.clone().intersect(interval2);
        assert_eq!(result.len(), 1);
        assert_eq!(result[0], Interval::closed(3, 5));

        let interval3 = Interval::closed(6, 10);
        let result = interval1.intersect(interval3);
        assert_eq!(result.len(), 2);
        assert_eq!(result[0], Interval::closed(1, 5));
        assert_eq!(result[1], Interval::closed(6, 10));
    }

    #[test]
    fn test_interval_diff() {
        let interval1 = Interval::closed(1, 5);
        let interval2 = Interval::closed(3, 7);
        let result = interval1.clone().diff(interval2);
        assert_eq!(result.len(), 2);
        assert_eq!(result[0], Interval::closed(1, 3));
        assert_eq!(result[1], Interval::closed(5, 7));

        let interval3 = Interval::closed(6, 10);
        let result = interval1.clone().diff(interval3.clone());
        assert_eq!(result.len(), 2);
        assert_eq!(result[0], interval1);
        assert_eq!(result[1], interval3);
    }


    #[test]
    fn test_intersect_intervals() {
        let intervals = vec![
            Interval::closed(1, 5),
            Interval::closed(3, 7),
            Interval::closed(6, 10),
        ];
        let result = intersect_intervals(intervals);
        assert_eq!(result.len(), 2);
        assert_eq!(result[0], Interval::closed(3, 5));
        assert_eq!(result[1], Interval::closed(6, 10));
    }

    #[test]
    fn test_union_intervals() {
        let intervals = vec![
            Interval::closed(1, 5),
            Interval::closed(3, 7),
            Interval::closed(6, 10),
        ];
        let result = union_intervals(intervals);
        assert_eq!(result.len(), 1);
        assert_eq!(result[0], Interval::closed(1, 10));
    }
}
