//! Implementation of the MAXRECTS 2D packing algorithm based on
//! "A thousand Ways to Pack the Bin" by Jukka Jylänki
//! 
//! Available here: http://clb.demon.fi/files/RectangleBinPack.pdf

extern crate geom;    

use std::cmp::min;
use geom::{Rect, Size2D, Point2D};

/// Determines if a rectangle is a superset (contains all of) another rectangle
fn rect_supersets<T: Ord + Add<T,T>>(sup: &Rect<T>, sub: &Rect<T>) -> bool {
    sup.origin.x < sub.origin.x + sub.size.width  &&
    sup.origin.y < sub.origin.y + sub.size.height &&
    sup.origin.x + sup.size.width  > sub.origin.x &&
    sup.origin.y + sup.size.height > sub.origin.y
}

/// Calculates the best-short-side heuristic if applicaple, and returns `None`
/// if not.
fn bssf<T: Ord + Add<T,T> + Sub<T,T>>(sup: &Size2D<T>, sub: &Size2D<T>) -> Option<T>{
    if sup.width >= sub.width && sup.height >= sub.height {
        Some(min(sup.width - sub.width, sup.height - sub.height))
    } else {
        None
    }
}

pub struct RectPacker<T> {
    empty: Vec<Rect<T>>,
}

impl<T: Clone + Ord + Add<T,T> + Sub<T,T>> RectPacker<T> {
    /// Creates a new, empty RectPacker
    #[inline]
    pub fn new() -> RectPacker<T> {
        RectPacker{empty: Vec::new()}
    }

    /// Adds a rectangle to the list of free rectangles, so that another
    /// rectangle can be packed into it. This may be a previously packed
    /// and does not have to be disjoint of any previous free rectangle
    pub fn add_free(&mut self, free: Rect<T>) {
        self.empty.push(free);
    }

    /// Retrieves the free rectangle with the best rating (lowest heuristic)
    /// with respect to a certain size
    fn optimal(&self, size: &Size2D<T>) -> Option<(Point2D<T>, T)> {
        self.empty.iter()
            .filter_map(|x| if let Some(h) = bssf(&x.size, size) {Some((x,h))} else {None})
            .min_by(|&(_, ref h)| h.clone())
            .map(|(x,h)| (x.origin.clone(), h))
    }

    /// Packs a rectangle into a free rectangle, so that it does not intersect
    /// any previously packed rectangles. If a suitable location is found, it
    /// is returned, otherwise `None` is returned.
    pub fn pack(&mut self, size: &Size2D<T>) -> Option<Point2D<T>> {
        if let Some((position, _)) = self.optimal(size) {
            self.subtract_rect(&Rect(position.clone(), size.clone()));
            Some(position)
        } else {
            None
        }
    }

    /// Removes a rectangle from the list of free rectangles, so that no
    /// remaining free rectangle intersects with this rectangle
    fn subtract_rect(&mut self, newrect: &Rect<T>) {
        
        // We keep track of the 'derived' rectangles. These are the rectangles
        // at the end of the free list that were added earlier during the
        // process. Since we know these do not intersect `newrect` they can be
        // skipped.
        let mut derived = 0;
        let mut index = 0;
        while index < self.empty.len() - derived {
            let other = self.empty[index].clone();

            if other.intersects(newrect) {
                if newrect.origin.x < other.max_x() {
                    self.empty.push(Rect(
                        other.origin.clone(),
                        Size2D(newrect.origin.x - other.origin.x, other.size.height.clone())));
                    derived += 1;
                }

                if newrect.origin.y < other.max_y() {
                    self.empty.push(Rect(
                        other.origin.clone(),
                        Size2D(other.size.width.clone(), newrect.origin.y - other.origin.y)));
                    derived += 1;
                }

                if newrect.max_x() < other.max_x() {
                    self.empty.push(Rect(
                        Point2D(newrect.max_x(), other.origin.y.clone()),
                        Size2D(other.max_x() - newrect.max_x(), other.size.height.clone())));
                    derived += 1;
                }

                if newrect.max_y() < other.max_y() {
                    self.empty.push(Rect(
                        Point2D(other.origin.x.clone(), newrect.max_y()),
                        Size2D(other.size.width.clone(), other.max_y() - newrect.max_y())));
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

        // Compares all rectangles pairwise and removes any that is a subset
        // of another rectangle
        let mut i = 0;
        while i < self.empty.len() {
            let mut j = i + 1;
            while j < self.empty.len() {
                let (a,b) = (self.empty[i].clone(), self.empty[j].clone());
                if rect_supersets(&a,&b) {
                    self.empty.swap_remove(j);
                } else if rect_supersets(&b,&a) {
                    self.empty.swap_remove(i);
                    j = i + 1;
                } else {
                    j += 1;
                }
            }

            i += 1;
        }
    }

    /// Packs a list rectangles by continually packing the best (by heuristic)
    /// packed rectangle. It may not be possible to pack all, elements, in
    /// which case the iterator will only yield the elements that were
    /// successfully packed.
    pub fn pack_global<'a, U, F: for<'b>FnMut<(&'b U,),Size2D<T>>>
        (&'a mut self, sizes: Vec<U>, mapping: F) -> GlobalPackIter<'a,T,U,F> {
        GlobalPackIter{
            packer: self,
            input: sizes,
            mapping: mapping,
        }
    }
}

pub struct GlobalPackIter<'a,T: 'a,U,F> {
    packer: &'a mut RectPacker<T>,
    input: Vec<U>,
    mapping: F,
}

impl<'a,T,U,F> GlobalPackIter<'a,T,U,F> {
    /// Whether all elements have been packed. It might not be possible to pack
    /// all elements, in which case this will return false even though the
    /// iterator yields `None`.
    pub fn all_packed(&self) -> bool {
        self.input.is_empty()
    }
}

impl<'a, T: Clone + Ord + Add<T,T> + Sub<T,T>, U, F: for<'a>FnMut<(&'a U,),Size2D<T>>>
    Iterator<(U,Rect<T>)> for GlobalPackIter<'a,T,U,F> {

    fn size_hint(&self) -> (uint, Option<uint>) {
        (0, Some(self.input.len()))
    }

    fn next(&mut self) -> Option<(U,Rect<T>)> {
        if self.input.is_empty() {
            None
        } else {
            let GlobalPackIter{
                ref mut packer,
                ref mut input,
                ref mut mapping,
            } = *self;

            let min = input.iter()
                .enumerate()
                .filter_map(|(index,x)| {
                    let size = mapping.call_mut((x,));
                    if let Some((point,heuristic)) = packer.optimal(&size) {
                        Some((index, Rect(point, size), heuristic))
                    } else {
                        None
                    }
                })
                .min_by(|&(_,_, ref heuristic)| heuristic.clone());

            if let Some((index, rect, _)) = min {
                let x = input.swap_remove(index).unwrap();
                packer.subtract_rect(&rect);
                Some((x, rect))
            } else {
                None
            }
        }
    }
}

#[cfg(test)]
mod test {
    use geom::{Rect, Point2D, Size2D};
    use super::{RectPacker};

    fn valid_pack<T: Ord + Clone + Add<T,T> + Sub<T,T>>(rectangles: &Vec<Rect<T>>) -> bool {
        for (i,x) in rectangles.iter().enumerate() {
            for (j,y) in rectangles.iter().enumerate() {
                if i != j && x.intersects(y) {
                    return false;
                }
            }
        }

        true
    }

    #[test]
    fn global_pack() {
        let mut packer = RectPacker::new();
        packer.add_free(Rect(Point2D(0,0), Size2D(100,100)));
        let a = vec![Size2D(1u,10), Size2D(9,9), Size2D(9,1)];
        assert!(valid_pack(&packer.pack_global(a, |&x| x).map(|(_,x)| x).collect()));
    }

    #[test]
    fn nonglobal_pack() {
        let mut packer = RectPacker::new();
        packer.add_free(Rect(Point2D(0u,0), Size2D(100,100)));

        println!("{}", packer.pack(&Size2D(1,10)).unwrap());
        println!("{}", packer.pack(&Size2D(9,9)).unwrap());
        println!("{}", packer.pack(&Size2D(9,1)).unwrap());
    }
}