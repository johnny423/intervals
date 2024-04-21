use std::cmp::Ordering;
use std::ops::Deref;

#[derive(Debug, Clone)]
pub enum Bound<T> {
    LeftInclusive(T),
    RightInclusive(T),
    Exclusive(T),
}

impl<T> Bound<T> {
    pub fn to_right(self) -> Self {
        match self {
            Bound::LeftInclusive(t) => { Bound::RightInclusive(t) }
            value => { value }
        }
    }

    pub fn to_left(self) -> Self {
        match self {
            Bound::RightInclusive(t) => { Bound::LeftInclusive(t) }
            value => { value }
        }
    }
}


impl<T> Deref for Bound<T> {
    type Target = T;

    fn deref(&self) -> &Self::Target {
        match self {
            Self::LeftInclusive(t) | Self::RightInclusive(t) | Self::Exclusive(t) => { t }
        }
    }
}


impl<T> PartialEq for Bound<T>
    where T: Eq
{
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (Bound::RightInclusive(t), Bound::RightInclusive(o)) |
            (Bound::Exclusive(t), Bound::Exclusive(o)) |
            (Bound::LeftInclusive(t), Bound::LeftInclusive(o)) => {
                t == o
            }
            _ => { false }
        }
    }
}

impl<T> Eq for Bound<T> where T: Eq {}

impl<T> PartialOrd for Bound<T>
    where T: Ord
{
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        match self.deref().cmp(other.deref()) {
            Ordering::Equal => {
                if self.eq(other) {
                    Some(Ordering::Equal)
                } else {
                    match (self, other) {
                        (Bound::RightInclusive(_), _) => { Some(Ordering::Greater) }
                        (Bound::LeftInclusive(_), _) => { Some(Ordering::Less) }
                        (_, _) => { unreachable!() }
                    }
                }
            }
            results => { Some(results) }
        }
    }
}

impl<T> Ord for Bound<T>
    where T: Ord
{
    fn cmp(&self, other: &Self) -> Ordering {
        self.partial_cmp(other).unwrap()
    }
}
