//! Implementation of the MAXRECTS 2D packing algorithm based on
//! "A thousand Ways to Pack the Bin" by Jukka Jylänki
//! 
//! Available here: http://clb.demon.fi/files/RectangleBinPack.pdf

extern crate cgmath;    

use std::cmp::{partial_min, Ordering};
use cgmath::{BaseNum, Aabb, Aabb2, Vector2, Point, Point2};

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

/// Whether a rectangle intersects another rectangle
fn intersects<S>(sup: &Aabb2<S>, sub: &Aabb2<S>) -> bool where S: BaseNum {
    sup.min.x < sub.max.x &&
    sup.min.y < sub.max.y &&
    sup.max.x > sub.min.x &&
    sup.max.y > sup.min.y
}

/// Determines if a rectangle is a superset of (contains all of) another rectangle
fn supersets<S>(sup: &Aabb2<S>, sub: &Aabb2<S>) -> bool where S: BaseNum {
    sup.min.x <= sub.min.x &&
    sup.min.y <= sub.min.y &&
    sup.max.x >= sub.max.x &&
    sup.max.y >= sup.max.y
}

/// Returns the best-short-side heuristic if applicaple, and `None` if not.
fn bssf<S>(sup: &Vector2<S>, sub: &Vector2<S>) -> Option<S> where S: BaseNum {
    if sup.x >= sub.x && sup.y >= sub.y {
        partial_min(sup.x - sub.x, sup.x - sub.x)
    } else {
        None
    }
}

pub struct RectPacker<S> where S: BaseNum {
    empty: Vec<Aabb2<S>>,
}

impl<S> RectPacker<S> where S: BaseNum {
    /// Creates a new, empty RectPacker
    #[inline]
    pub fn new() -> RectPacker<S> {
        RectPacker{empty: Vec::new()}
    }

    /// Adds a rectangle to the list of free rectangles, so that another rectangle can be packed
    /// into it. This does not have to be disjoint of any previous free rectangle. This may be a
    /// previously packed rectangle, but further optimal packing cannot be guarenteed in that case
    pub fn add_free(&mut self, free: Aabb2<S>) {
        self.empty.push(free);
    }

    /// Retrieves the free rectangle with the best rating (lowest heuristic) with respect to a
    /// certain size
    fn optimal(&self, size: &Vector2<S>) -> Option<(Point2<S>, S)> {
        self.empty.iter()
            .filter_map(|x| if let Some(h) = bssf(&x.dim(), size) {Some((x,h))} else {None})
            .min_cmp(|&(_, ref a), &(_, ref b)| a.partial_cmp(b).unwrap_or(Ordering::Equal))
            .map(|(x,h)| (x.min.clone(), h))
    }

    /// Packs a rectangle into a free rectangle, so that it does not intersect any previously
    /// packed rectangles. If a suitable location is found, it is returned, otherwise `None`
    /// is returned.
    pub fn pack(&mut self, size: &Vector2<S>) -> Option<Point2<S>> {
        if let Some((position, _)) = self.optimal(size) {
            self.subtract_rect(&Aabb2::new(position.clone(), position.add_v(size)));
            Some(position)
        } else {
            None
        }
    }

    /// Removes a rectangle from the list of free rectangles, so that no remaining free rectangle
    /// intersects with this rectangle
    fn subtract_rect(&mut self, sub: &Aabb2<S>) {
        
        // We keep track of the 'derived' rectangles. These are the rectangles at the end of the
        // free list that were added earlier during the process. Since we know these do not
        // intersect `sub` they can be skipped.
        let mut derived = 0;
        let mut index = 0;
        while index < self.empty.len() - derived {

            let free = self.empty[index].clone();

            if intersects(&free, sub) {
                if sub.min.x > free.min.x {
                    self.empty.push(Aabb2::new(
                        free.min.clone(),
                        Point2::new(sub.min.x, free.max.y)));
                    derived += 1;
                }

                if sub.min.y > free.min.y {
                    self.empty.push(Aabb2::new(
                        free.min.clone(),
                        Point2::new(free.max.x, sub.min.y)));
                    derived += 1;
                }

                if sub.max.x < free.max.x {
                    self.empty.push(Aabb2::new(
                        Point2::new(sub.max.x, free.min.y),
                        free.max.clone()));
                    derived += 1;
                }

                if sub.max.y < free.max.y {
                    self.empty.push(Aabb2::new(
                        Point2::new(free.min.x, sub.max.y),
                        free.max.clone()));
                    derived += 1;
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
                if supersets(&a,&b) {
                    self.empty.swap_remove(j);
                } else if supersets(&b,&a) {
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
    /// object with the best (by heuristic) possible packing. If not all elements can be packed, 
    /// the iterator will only yield the elements that were successfully packed.
    ///
    /// Global packing is often better than normal packing, but is also slower.
    pub fn pack_global_by<'a, U, F>(&'a mut self, sizes: Vec<U>, mapping: F)
        -> GlobalPackIter<'a,S,U,F> where
        F:  for<'b>FnMut(&'b U) -> Vector2<S>
    {
        GlobalPackIter{
            packer: self,
            input: sizes,
            mapping: mapping,
        }
    }

    /// Packs a list rectangles by continually packing the rectangle with the best (by heuristic)
    /// packing. If not all elements can be packed, the iterator will only yield the elements that
    /// were successfully packed.
    ///
    /// Global packing is often better than normal packing, but is also slower.
    pub fn pack_global<'a>(&'a mut self, sizes: Vec<Vector2<S>>) ->
        GlobalPackIter<'a, S, Vector2<S>, fn(&Vector2<S>) -> Vector2<S>> where
        S: Clone
    {
        fn identity<S>(a: &Vector2<S>) -> Vector2<S> where S: Clone {
            a.clone()
        }

        GlobalPackIter{
            packer: self,
            input: sizes,
            mapping: identity as fn(&Vector2<S>) -> Vector2<S>,
        }
    }
}

pub struct GlobalPackIter<'a, S: 'a, U, F> where
    F: for<'b>FnMut(&'b U) -> Vector2<S>
{
    packer: &'a mut RectPacker<S>,
    input: Vec<U>,
    mapping: F,
}

impl<'a,S,U,F> GlobalPackIter<'a,S,U,F> where F: for<'b>FnMut(&'b U) -> Vector2<S> {
    /// Whether all elements have been packed. It might not be possible to pack all elements,
    /// in which case this will return false even though the iterator yields `None`.
    pub fn all_packed(&self) -> bool {
        self.input.is_empty()
    }
}


impl<'a,S,U,F> Iterator for GlobalPackIter<'a,S,U,F> where
    S: BaseNum, F: for<'b>FnMut(&'b U) -> Vector2<S> {

    type Item = (U, Aabb2<S>);

    fn size_hint(&self) -> (usize, Option<usize>) {
        (0, Some(self.input.len()))
    }

    fn next(&mut self) -> Option<(U,Aabb2<S>)> {
        let GlobalPackIter{
            ref mut packer,
            ref mut input,
            ref mut mapping,
        } = *self;

        let min = input.iter()
            .enumerate()
            .filter_map(|(index,x)| {
                let size = mapping(x);
                if let Some((point,heuristic)) = packer.optimal(&size) {
                    Some((index, Aabb2::new(point, point.add_v(&size)), heuristic))
                } else {
                    None
                }
            })
            .min_cmp(|&(_, _, ref a), &(_, _, ref b)| a.partial_cmp(b).unwrap_or(Ordering::Equal));

        if let Some((index, rect, _)) = min {
            let x = input.swap_remove(index);
            packer.subtract_rect(&rect);
            Some((x, rect))
        } else {
            None
        }
    }
}

#[cfg(test)]
mod test {
    use cgmath::{BaseNum, Aabb, Aabb2, Vector2, Point, Point2};
    use super::{intersects, RectPacker};

    fn valid_pack<S: BaseNum>(rectangles: &Vec<Aabb2<S>>) -> bool {
        for (i,x) in rectangles.iter().enumerate() {
            for (j,y) in rectangles.iter().enumerate() {
                if i != j && intersects(x, y) {
                    return false;
                }
            }
        }

        true
    }

    #[test]
    fn global_pack() {
        let mut packer = RectPacker::new();
        packer.add_free(Aabb2::new(Point2::new(0,0), Point2::new(100,100)));
        let a = vec![Vector2::new(1,10), Vector2::new(9,9), Vector2::new(9,1)];
        assert!(valid_pack(&packer.pack_global(a).map(|(_,x)| x).collect()));
    }

    #[test]
    fn normal_pack() {
        let mut packer = RectPacker::new();
        packer.add_free(Aabb2::new(Point2::new(0,0), Point2::new(100,100)));

        println!("{:?}", packer.pack(&Vector2::new(1,10)).unwrap());
        println!("{:?}", packer.pack(&Vector2::new(9,9)).unwrap());
        println!("{:?}", packer.pack(&Vector2::new(9,1)).unwrap());
    }
}
