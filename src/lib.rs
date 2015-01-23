//! Implementation of the MAXRECTS 2D packing algorithm based on
//! "A thousand Ways to Pack the Bin" by Jukka Jylänki
//! 
//! Available here: http://clb.demon.fi/files/RectangleBinPack.pdf

#![allow(unstable)]

use std::fmt;
use std::ops::{Add, Sub};
use std::cmp::{partial_min, Ordering};

trait MinMaxIteratorExt: Iterator + Sized {
    fn min_cmp<F>(self, mut compare: F) -> Option<Self::Item> where
        F: FnMut(&Self::Item, &Self::Item) -> Ordering
    {
        self.fold(None, |min, x| {
            if let Some(minv) = min {
                match compare(&minv, &x) {
                    Ordering::Greater => Some(x),
                    _ => Some(minv)
                }
            } else {
                Some(x)
            }
        })
    }

    fn max_cmp<F>(self, mut compare: F) -> Option<Self::Item> where
        F: FnMut(&Self::Item, &Self::Item) -> Ordering
    {
        self.fold(None, |min, x| {
            if let Some(minv) = min {
                match compare(&minv, &x) {
                    Ordering::Less => Some(x),
                    _ => Some(minv)
                }
            } else {
                Some(x)
            }
        })
    }
}

impl<I> MinMaxIteratorExt for I where I: Iterator {}

#[derive(Clone)]
struct Rectangle<S> {
    min: (S,S),
    max: (S,S),
}

impl<S> Rectangle<S> {
    fn new(min: (S,S), max: (S,S)) -> Rectangle<S> {
        Rectangle{min: min, max: max}
    }
}

impl<S> Rectangle<S> where S: PartialOrd {
    /// Whether a rectangle intersects another rectangle
    fn intersects(&self, other: &Rectangle<S>) -> bool {
        self.min.0 < other.max.0 &&
        self.min.1 < other.max.1 &&
        self.max.0 > other.min.0 &&
        self.max.1 > other.min.1
    }

    /// Determines if a rectangle is a superset of (contains all of) another rectangle
    fn supersets(&self, other: &Rectangle<S>) -> bool {
        self.min.0 <= other.min.0 &&
        self.min.1 <= other.min.1 &&
        self.max.0 >= other.max.0 &&
        self.max.1 >= other.max.1
    }
}

impl<S> Rectangle<S> where S: Clone + PartialOrd + Sub<S, Output=S> {
    fn dimensions(&self) -> (S,S) {
        (self.max.0.clone() - self.min.0.clone(), self.max.1.clone() - self.min.1.clone())
    }
}

/// Returns the best-short-side heuristic if applicaple, and `None` if not.
fn bssf<S>(sup: &(S,S), sub: &(S,S)) -> Option<S> where S: Clone + PartialOrd + Sub<S, Output=S> {
    if sup.0 >= sub.0 && sup.1 >= sub.1 {
        partial_min(sup.0.clone() - sub.0.clone(), sup.1.clone() - sub.1.clone())
    } else {
        None
    }
}
pub struct FailedPacking<T,S> {
    partial_packed: Vec<(T, (S,S))>,
    original: Vec<T>,
}

impl<T,S> fmt::Display for FailedPacking<T,S> {
    fn fmt(&self, formatter: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        formatter.write_str("No possible rectangle packing found")
    }
}

impl<T,S> FailedPacking<T,S> {
    /// Yields the input the failed pack function was provided with, but in an arbitrary order
    pub fn restore(mut self) -> Vec<T> {
        for (i, _) in self.partial_packed.into_iter() {
            self.original.push(i);
        }

        self.original
    }
}

pub struct RectPacker<S> where S: Clone + PartialOrd + Add<S, Output=S> + Sub<S, Output=S> {
    empty: Vec<Rectangle<S>>,
}

impl<S> RectPacker<S> where S: Clone + PartialOrd + Add<S, Output=S> + Sub<S, Output=S> {
    /// Creates a new, empty RectPacker
    #[inline]
    pub fn new() -> RectPacker<S> {
        RectPacker{empty: Vec::new()}
    }

    /// Adds a rectangle defined by a minimum coordinate and a maximum coordinate to the list of
    /// free rectangles, so that another rectangle can be packed  into it. This interval is half-
    /// open: `min` is considered to be inside the rectangle while `max` is not.
    ///
    /// This does not have to be disjoint of any previous free rectangle. This may be a previously
    /// packed rectangle, but further optimal packing cannot be guarenteed in that case.
    ///
    /// # Panics
    /// 
    /// Panics if either x or y in `min` is more than `max`
    pub fn add_free(&mut self, min: (S,S), max: (S,S)) {
        if min.0 > max.0 {
            panic!("min.0 cannot be more than max.0");
        }

        if min.1 > max.1 {
            panic!("min.1 cannot be more than max.1");
        }

        self.empty.push(Rectangle::new(min, max));
    }

    /// Retrieves the best (by heuristic) free rectangle within a certain size.
    fn optimal(&self, size: &(S,S)) -> Option<((S,S), S)> {
        self.empty.iter()
            .filter_map(|x| bssf(&x.dimensions(), size).map(|h| (x,h)))
            .min_cmp(|&(_, ref a), &(_, ref b)| a.partial_cmp(b).unwrap_or(Ordering::Equal))
            .map(|(x,h)| (x.min.clone(), h))
    }

    /// Packs a rectangle into a free rectangle, so that it does not intersect any previously
    /// packed rectangles. If a suitable position is found, it is returned. Otherwise `None`
    /// is returned.
    pub fn pack(&mut self, width: S, height: S) -> Option<(S, S)> {
        //TODO: Check for negative width and height

        if let Some((position, _)) = self.optimal(&(width.clone(), height.clone())) {
            let max = (position.0.clone() + width, position.1.clone() + height);
            self.subtract_rect(&Rectangle::new(position.clone(), max));
            Some(position)
        } else {
            None
        }
    }

    /// Removes a rectangle from the list of free rectangles, so that no remaining free rectangle
    /// intersects with this rectangle
    fn subtract_rect(&mut self, sub: &Rectangle<S>) {
        
        // We keep track of the 'derived' rectangles. These are the rectangles at the end of the
        // free list that were added earlier during the process. Since we know these do not
        // intersect `sub` they can be skipped.
        let mut derived = 0;
        let mut index = 0;
        while index < self.empty.len() - derived {

            let free = self.empty[index].clone();

            if free.intersects(sub) {
                {
                    let mut push = |&mut: min, max| self.empty.push(Rectangle::new(min,max));

                    if sub.min.0 > free.min.0 {
                        push(free.min.clone(),(sub.min.0.clone(), free.max.1.clone()));
                        derived += 1;
                    }

                    if sub.min.1 > free.min.1 {
                        push(free.min.clone(), (free.max.0.clone(), sub.min.1.clone()));
                        derived += 1;
                    }

                    if sub.max.0 < free.max.0 {
                        push((sub.max.0.clone(), free.min.1.clone()), free.max.clone());
                        derived += 1;
                    }

                    if sub.max.1 < free.max.1 {
                        push((free.min.0.clone(), sub.max.1.clone()), free.max.clone());
                        derived += 1;
                    }
                }

                self.empty.swap_remove(index);

                // If derived rectangles have been added to the end, we do not
                // intersect it, and we can skip it.
                if derived > 0 {
                    derived -= 1;
                    index += 1;
                }
            } else {
                index += 1;
            }
        }

        // Compares all rectangles pairwise and removes any that is a subset of another rectangle
        let mut i = 0;
        while i < self.empty.len() {
            let mut j = i + 1;
            while j < self.empty.len() {
                let (a,b) = (self.empty[i].clone(), self.empty[j].clone());
                if a.supersets(&b) {
                    self.empty.swap_remove(j);
                } else if b.supersets(&a) {
                    self.empty.swap_remove(i);
                    j = i + 1;
                } else {
                    j += 1;
                }
            }

            i += 1;
        }
    }

    /// Maps a number of objects to rectangle sizes using `mapping` and continually packs the 
    /// object with the best (by heuristic) possible packing. Fails if all elements cannot be 
    /// packed. The returned `Vec` is an arbitrary permutation of the input with asscociated
    /// positions
    ///
    /// Global packing is often better than normal packing, but is also slower.
    pub fn pack_global<T,F>(&mut self, mut objects: Vec<T>, mut mapping: F)
        -> Result<Vec<(T,(S,S))>, FailedPacking<T,S>>
        where F:  for<'a>FnMut(&'a T) -> (S,S)
    {
        let mut packed = Vec::new();

        loop {
            let min = objects.iter()
                .enumerate()
                .filter_map(|(index,x)| {
                    let size = mapping(x);
                    self.optimal(&size).map(move |(pos, h)| ((index, pos, size), h))
                })
                .min_cmp(|&(_,ref a), &(_,ref b)| a.partial_cmp(b).unwrap_or(Ordering::Equal))
                .map(|(x,_)| x);

            if let Some((index, (x,y), (xsize, ysize))) = min {
                let element = objects.swap_remove(index);
                let max = (x.clone() + xsize, y.clone() + ysize);
                self.subtract_rect(&Rectangle::new((x.clone(),y.clone()), max));
                packed.push((element, (x, y)));
            } else {
                return if objects.is_empty() {
                    Ok(packed)
                } else {
                    Err(FailedPacking{partial_packed: packed, original: objects})
                }
            }
        }
    }
}

#[cfg(test)]
mod test {
    use super::{Rectangle, RectPacker};

    fn valid_pack(rectangles: &Vec<((u32,u32),(u32,u32))>) -> bool {
        let as_rectangles = |&:| rectangles.iter().map(|&((x,y),(width,height))|
            Rectangle::new((x,y), (x + width, x + height)));

        for (i,a) in as_rectangles().enumerate() {
            for (j,b) in as_rectangles().enumerate() {
                if i != j && a.intersects(&b) {
                    return false;
                }
            }
        }

        true
    }

    #[test]
    fn global_pack() {
        let mut packer = RectPacker::new();
        packer.add_free((0,0), (100,100));
        let a = vec![(1,10), (9,9), (9,1)];
        assert!(valid_pack(&packer.pack_global(a, |x| x.clone()).unwrap()));
    }

    #[test]
    fn normal_pack() {
        let mut packer = RectPacker::new();
        packer.add_free((0,0), (100,100));

        println!("{:?}", packer.pack(1,10).unwrap());
        println!("{:?}", packer.pack(9,9).unwrap());
        println!("{:?}", packer.pack(9,1).unwrap());
    }
}